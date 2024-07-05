#!/usr/bin/env python3

import argparse
import re

class Clause:
    def __init__(self, w1, w2, lits, wnext):
        self.watches, self.lits, self.wnext = set((w1, w2)), lits, wnext

    def __repr__(self): return '{}'.format(self.lits)

class Solver:
    def __init__(self):
        self.nvars = 0
        self.clauses = []
        self.watch = {}
        self.units = set()
        self.assign = {} # var -> True/False

    def add_clause(self, c):
        # mem looks like: [watch1] [watch2] [size] [lit1] [lit2] [lit3]
        c = list(set(c))
        self.nvars = max(self.nvars, *(abs(x) for x in c))
        x, y = c[0], c[1]
        w1 = self.watch.get(x, 0) if len(c) > 1 else -1
        w2 = self.watch.get(y, 0) if len(c) > 1 else -1
        self.clauses.append(Clause(x,y,c,{x: w1, y: w2}))
        if len(c) > 1:
            self.watch[x], self.watch[y] = len(self.clauses)-1, len(self.clauses)-1
        else:
            self.units.add(x)

    def solve(self):
        trail = [(v,None) for v in self.units]  # pairs of (var, reason)
        levels = [0]  # maps level # -> start index in trail
        tp = 0  # Next unprocessed trail item
        while len(self.assign) < self.nvars:
            print('assignments: {}'.format(self.assign))
            # Propagate pending implications
            while tp < len(trail):
                wl, reason = trail[tp]
                print('Propagating {} (reason: {})'.format(wl, reason))
                wp = self.watch.get(-wl, 0)
                while wp > 0:
                    # Try to find another lit to watch
                    clause = self.clauses[wp]
                    print('  Finding another watch for {} except {}'.format(clause.lits, clause.watches))
                    for l in clause.lits:
                        if l in clause.watches: continue
                        if self.assign.get(abs(l)) is None:
                            print('    watching {} instead'.format(l))
                            clause.watches.remove(wl)
                            clause.watches.add(l)
                            break
                    # Did we fail in finding another watch?
                    if -wl in clause.watches:
                        forced = (clause.watches - {-wl}).pop()
                        if self.assign.get(abs(forced)) == (forced < 0):
                            print('Conflict with {} and trail: {}'.format(forced, trail))
                            print('self.assign.get(abs({})) = {}'.format(forced, self.assign.get(abs(forced))))
                            import sys; sys.exit(-1)
                        elif self.assign.get(abs(forced)) == (forced > 0):
                            print('  {} already true, moving on...'.format(forced))
                        else:
                            print('  {} forced by {}, adding to trail and assigning'.format(forced, clause.lits))
                            self.assign[abs(forced)] = forced > 0
                            trail.append((forced, clause))
                    wp = clause.wnext[-wl]
                    print('  Moving on to wp = {}'.format(wp))
                print('  Done exploring watch list for {}'.format(-wl))
                tp += 1

            # Start a new level
            v = (range(1,self.nvars+1) - self.assign.keys()).pop()
            print('Choosing {}'.format(v))  # TODO: default to negative polarity
            self.assign[v] = False
            levels.append(len(trail))
            trail.append((v, None))
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


    s = Solver()
    for c in clauses:
        s.add_clause(c)
    s.solve()
