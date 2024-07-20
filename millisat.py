#!/usr/bin/env python3

import argparse
import re
import sys

LOG = 2

class WatchList:
    def __init__(self):
        self.clauses, self.pos, self.size = [], {}, 0

    def add(self, clause):
        self.pos[clause] = len(self.clauses)
        self.clauses.append(clause)
        self.size += 1

    def remove(self, clause):
        self.clauses[self.pos[clause]] = None
        del self.pos[clause]
        self.size -= 1
        if self.size < len(self.clauses) // 2:
            self.clauses = [x for x in self.clauses if x is not None]
            self.pos = {x: i for i, x in enumerate(self.clauses)}

    def entries(self):
        yield from (c for c in self.clauses if c is not None)

class Clause:
    def __init__(self, watch1, watch2, lits):
        self.watches, self.lits = set((watch1, watch2)), lits

    def __repr__(self):
        x = [f'{l}*' if l in self.watches else str(l) for l in self.lits]
        return '{' + ', '.join(x) + '}'

class Solver:
    def __init__(self, nvars):
        self.nvars = nvars
        self.clauses = []
        self.watch = dict(((x, WatchList()) for x in range(-nvars,nvars+1) if x != 0))
        self.polarity = dict((v, 0) for v in range(1,nvars+1))
        self.units = set()
        self.assign = {} # var -> True/False
        self.unsat = False

    def add_clause(self, c, watch1=None, watch2=None):
        c = list(set(c))
        assert max((abs(x) for x in c), default=0) <= self.nvars
        if len(c) == 1: self.units.add(c[0])
        if len(c) == 0: self.unsat = True
        if len(c) <= 1: return None
        x = watch1 or c[0]
        y = (watch2 or c[0]) if (watch1 and x != c[0]) else (watch2 or c[1])
        clause = Clause(x,y,c)
        self.clauses.append(clause)
        self.watch[x].add(clause)
        self.watch[y].add(clause)
        return clause

    def solve(self):
        if self.unsat: return False
        trail = [(l,None,0) for l in self.units]  # tuples of (lit, reason, level)
        for unit in self.units:
            if abs(unit) in self.assign and (unit > 0) != self.assign[abs(unit)]:
                return False  # Conflicting units
            self.assign[abs(unit)] = unit > 0
        curr_level = 0
        levels = [0]  # maps level # -> start index in trail
        level = {}
        tp = 0  # Next unprocessed trail item
        while len(self.assign) < self.nvars or tp < len(trail):
            if LOG > 1: print('assignments: {}'.format(self.assign))
            # Propagate pending implications
            while tp < len(trail):
                wl, reason, _ = trail[tp]
                if LOG > 1: print('Propagating {} (reason: {})'.format(wl, reason))
                if LOG > 1: print('Trail: {}'.format(trail))
                level[abs(wl)] = curr_level
                for clause in self.watch[-wl].entries():
                    other_w = (clause.watches - {-wl}).pop()  # TODO: make this clause.other_watch(-wl)
                    if self.assign.get(abs(other_w)) == (other_w > 0):
                        if LOG > 1: print('  Other watch {} is already true, skipping'.format(other_w))
                        continue
                    if LOG > 1: print('  Finding another watch for {}'.format(clause))
                    if LOG > 1:
                        print('    assignments: {}'.format(dict([abs(l), self.assign.get(abs(l))] for l in clause.lits)))
                    for l in clause.lits:
                        if l in clause.watches: continue
                        if self.assign.get(abs(l)) is None or self.assign.get(abs(l)) == (l > 0):
                            if LOG > 1: print('    watching {} instead'.format(l))
                            clause.watches.remove(-wl)
                            clause.watches.add(l)
                            self.watch[-wl].remove(clause)
                            self.watch[l].add(clause)
                            break
                    # Did we fail in finding another watch?
                    if -wl in clause.watches:
                        forced = (clause.watches - {-wl}).pop()  # TODO: make this clause.other_watch(-wl)
                        if self.assign.get(abs(forced)) == (forced < 0):
                            if LOG > 1: print('Conflict with lit {}, clause {} and trail: {}. Resolving...'.format(forced, clause, trail))
                            if curr_level == 0: return False  # UNSAT
                            stamp = dict((-l, True) for l in clause.lits)
                            if LOG > 1: print('stamped: {}'.format(stamp))
                            resolved = set(clause.lits)
                            #trail.append((forced, clause, curr_level))
                            backjump_level = curr_level
                            # Resolve a conflict
                            for tl, tc, tlev in reversed(trail):
                                if tc is None: continue  # Decision
                                if stamp.get(tl):
                                    if LOG > 1: print('   resolving with {} on level {} since {} is stamped'.format(tc, tlev, tl))
                                    for l in tc.lits:
                                        if l != tl: stamp[-l] = True
                                        if -l in resolved:
                                            resolved.remove(-l)
                                        else:
                                            resolved.add(l)
                                    if LOG > 1: print('      current resolved clause: {}'.format(resolved))
                                    lcount = sum(1 for l in resolved if level[abs(l)] == curr_level)
                                    if lcount == 1:
                                        backjump_level = max((level[abs(l)] for l in resolved if level[abs(l)] < curr_level), default=0)
                                        break
                            # Need to watch l and a lit on backjump_level
                            new_l = [l for l in resolved if level[abs(l)] == curr_level][0]
                            bj_lits = [l for l in resolved if level[abs(l)] == backjump_level]
                            new_watch = bj_lits[0] if bj_lits else None  # There will be one bj_lit unless resolved is unit.
                            while trail and trail[-1][-1] > backjump_level:
                                l, r, llev  = trail.pop()
                                print('  pop {}'.format((l,r,llev)))
                                del self.assign[abs(l)]
                                del level[abs(l)]
                            tp = len(trail)-1
                            self.assign[abs(new_l)] = new_l > 0
                            # TODO: could compute the other lit to watch when we compute backjump_level
                            # TODO2
                            resolved_clause = self.add_clause(resolved, new_l, new_watch)
                            if LOG > 0: print('[[ Installing resolved clause {} for {} at the end of level {} ]]'.format(resolved_clause, new_l, backjump_level))
                            trail.append((new_l, resolved_clause, backjump_level))
                            level[abs(new_l)] = backjump_level
                            curr_level = backjump_level
                            break
                        elif self.assign.get(abs(forced)) == (forced > 0):
                            if LOG > 1: print('  {} already true, moving on...'.format(forced))
                        else:
                            if LOG > 1: print('  {} forced by {}, adding to trail and assigning'.format(forced, clause.lits))
                            self.assign[abs(forced)] = forced > 0
                            self.polarity[abs(forced)] += 1 if forced > 0 else -1
                            trail.append((forced, clause, curr_level))
                            level[abs(forced)] = curr_level
                if LOG > 1: print('  Done exploring watch list for {}'.format(-wl))
                tp += 1

            if len(self.assign) == self.nvars: break

            # Start a new level
            v = (range(1,self.nvars+1) - self.assign.keys()).pop()
            if LOG > 1: print('Trail: {}'.format(trail))
            self.assign[v] = True if self.polarity[v] > 0 else False
            print('Choosing {} = {}'.format(v, self.assign[v]))
            curr_level += 1
            level[v] = curr_level
            levels.append(len(trail))
            trail.append(((1 if self.assign[v] else -1) * v, None, curr_level))

        return True

def parse_dimacs(s):
    header = None
    clauses = []
    watches = {}
    max_var = 0
    carryover = []
    for i, line in enumerate(s.split('\n')):
        if line.startswith('c'): continue
        if header is None:
            header = re.match(r'p\s+cnf\s+(\d+)\s+(\d+)', line)
            if header is None: raise ValueError('Line {}: Expected header, got: "{}"'.format(i, line))
            continue
        lits = carryover + [l.strip() for l in line.split()]
        if len(lits) == 0: continue
        if lits[-1] != '0':
            carryover = lits
            continue
        else:
            carryover = []
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
        assignments = [l * (1 if v else -1) for l,v in sorted(s.assign.items())]
        stride = 10
        for i in range(0, len(assignments), stride):
            end = ''
            if i + stride >= len(assignments):
                end = " 0"
            print('v {}{}'.format(' '.join((str(x) for x in assignments[i:i+stride])), end))
        print('s SATISFIABLE')
        sys.exit(10)
    else:
        print('s UNSATISFIABLE')
        sys.exit(20)
