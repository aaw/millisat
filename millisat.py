#!/usr/bin/env python3

import argparse
import re

class WatchList:
    def __init__(self):
        self.clauses = []
        self.pos = {}
        self.size = 0

    def add(self, clause):
        self.pos[clause] = len(self.clauses)
        self.clauses.append(clause)
        self.size += 1

    def remove(self, clause):
        self.clauses[self.pos[clause]] = None
        del self.pos[clause]
        self.size -= 1
        if self.size < len(self.clauses) // 2:
            self._compact()

    def entries(self):
        for c in self.clauses:
            if c is None: continue
            yield c

    def _compact(self):
        compacted = []
        for i, clause in enumerate(self.clauses):
            if clause is None: continue
            self.pos[clause] = len(compacted)
            compacted.append(clause)
        self.clauses = compacted

class Clause:
    def __init__(self, w1, w2, lits):
        self.watches, self.lits = set((w1, w2)), lits

    def __repr__(self): return '{}'.format(self.lits)

class Solver:
    def __init__(self, nvars):
        self.nvars = nvars
        self.clauses = []
        self.watch = dict(((x, WatchList()) for x in range(-nvars,nvars+1) if x != 0))
        self.units = set()
        self.assign = {} # var -> True/False

    def add_clause(self, c):
        c = list(set(c))
        assert max(abs(x) for x in c) <= self.nvars
        if len(c) == 1:
            self.units.add(c[0])
            return
        x, y = c[0], c[1]
        clause = Clause(x,y,c)
        self.clauses.append(clause)
        self.watch[x].add(clause)
        self.watch[y].add(clause)

    def solve(self):
        trail = [(l,None,0) for l in self.units]  # tuples of (lit, reason, level)
        for unit in self.units:
            if abs(unit) in self.assign and (unit > 0) != self.assign[abs(unit)]:
                return False  # Conflicting units
            self.assign[abs(unit)] = unit > 0
        curr_level = 0
        levels = [0]  # maps level # -> start index in trail
        level = {}
        tp = 0  # Next unprocessed trail item
        while len(self.assign) < self.nvars:
            print('assignments: {}'.format(self.assign))
            # Propagate pending implications
            while tp < len(trail):
                wl, reason, _ = trail[tp]
                print('Propagating {} (reason: {})'.format(wl, reason))
                print('Trail: {}'.format(trail))
                level[abs(wl)] = curr_level
                for clause in self.watch[-wl].entries():
                    print('  Finding another watch for {} except {}'.format(clause.lits, clause.watches))
                    for l in clause.lits:
                        if l in clause.watches: continue
                        if self.assign.get(abs(l)) is None:
                            print('    watching {} instead'.format(l))
                            clause.watches.remove(-wl)
                            clause.watches.add(l)
                            self.watch[-wl].remove(clause)
                            self.watch[l].add(clause)
                            break
                    # Did we fail in finding another watch?
                    if -wl in clause.watches:
                        forced = (clause.watches - {-wl}).pop()
                        if self.assign.get(abs(forced)) == (forced < 0):
                            print('Conflict with lit {}, clause {} and trail: {}. Resolving...'.format(forced, clause, trail))
                            if curr_level == 0: return False  # UNSAT
                            stamp = dict((-l, True) for l in clause.lits)
                            resolved = set(clause.lits)
                            trail.append((forced, clause, curr_level))
                            backjump_level = curr_level
                            for tl, tc, _ in reversed(trail):
                                if tc is None: continue
                                if stamp.get(tl):
                                    for l in tc.lits:
                                        stamp[-l] = True
                                        if -l in resolved:
                                            resolved.remove(-l)
                                        else:
                                            resolved.add(l)
                                    lcount = sum(1 for l in resolved if level[abs(l)] == curr_level)
                                    if lcount == 1:
                                        print('FINAL RESOLVED: {}'.format(resolved))
                                        backjump_level = max((l for l in resolved if level[abs(l)] < curr_level), default=0)
                                        print('NEW LEVEL: {}'.format(backjump_level))
                                        break
                            new_l = [l for l in resolved if level[abs(l)] == curr_level][0]
                            while trail and trail[-1][-1] > backjump_level:
                                l, r, _  = trail.pop()
                                if abs(l) in self.assign: del self.assign[abs(l)]
                                if abs(l) in level: del level[abs(l)]
                            tp = len(trail)-1
                            self.assign[abs(new_l)] = new_l > 0
                            trail.append((new_l, list(resolved), backjump_level))
                            level[abs(new_l)] = backjump_level
                            curr_level = backjump_level
                            break
                        elif self.assign.get(abs(forced)) == (forced > 0):
                            print('  {} already true, moving on...'.format(forced))
                        else:
                            print('  {} forced by {}, adding to trail and assigning'.format(forced, clause.lits))
                            self.assign[abs(forced)] = forced > 0
                            trail.append((forced, clause, curr_level))
                            level[abs(forced)] = curr_level
                print('  Done exploring watch list for {}'.format(-wl))
                tp += 1

            if len(self.assign) == self.nvars: break

            # Start a new level
            v = (range(1,self.nvars+1) - self.assign.keys()).pop()
            print('Trail: {}'.format(trail))
            print('Choosing {}'.format(v))
            self.assign[v] = False
            curr_level += 1
            level[v] = curr_level
            levels.append(len(trail))
            trail.append((-v, None, curr_level))

        return True

def parse_dimacs(s):
    header = None
    clauses = []
    watches = {}
    max_var = 0
    for i, line in enumerate(s.split('\n')):
        if line.startswith('c'): continue
        if header is None:
            header = re.match(r'p cnf (\d+) (\d+)', line)
            if header is None: raise ValueError('Line {}: Expected header, got: "{}"'.format(i, line))
            continue
        lits = line.split()
        if len(lits) == 0: continue
        if lits[-1] != '0': raise ValueError('Line {}: Expected 0 as clause terminator, got "{}"'.format(i, line))
        lits = [int(l) for l in lits[:-1]]
        max_var = max(max_var, *(abs(x) for x in lits)) if lits else max_var
        clauses.append(lits)
    num_vars, num_clauses = (int(x) for x in header.groups())
    if len(clauses) != num_clauses:
        raise ValueError('Inconsistent clause count in header vs. file ({} vs. {})'.format(num_clauses, len(clauses)))
    if max_var > num_vars:
        raise ValueError('Inconsistent number of variables in header vs. file ({} vs. {})'.format(num_vars, max_var))
    return num_vars, clauses

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='A CDCL solver')
    parser.add_argument('filename', type=str, help='Path to a DIMACS CNF file')
    args = parser.parse_args()

    num_vars, clauses = parse_dimacs(open(args.filename).read())
    print('{} vars, {} clauses'.format(num_vars, len(clauses)))
    for clause in clauses:
        print(clause)


    s = Solver(num_vars)
    for c in clauses:
        s.add_clause(c)
    if s.solve():
        assignments = [l * (1 if v else -1) for l,v in s.assign.items()]
        stride = 10
        for i in range(0, len(assignments), stride):
            print('v {} 0'.format(' '.join((str(x) for x in assignments[i:i+stride]))))
        print('s SATISFIABLE')
    else:
        print('s UNSATISFIABLE')
