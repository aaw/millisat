#!/usr/bin/env python3

import argparse
import itertools
import re
import sys

G = 0.9999  # Armin Biere's agility multiplier
LOG = 0

class Clause:
    def __init__(self, lits, watch1, watch2):
        self.lits, self.watches = lits, set((watch1, watch2))

    def other_watch(self, watch):
        assert watch in self.watches; return (self.watches - {watch}).pop()

    def __repr__(self):
        return '(' + ' '.join([f'{l}*' if l in self.watches else str(l) for l in self.lits]) + ')'

class Solver:
    # A literal can either agree with its variable assignment, disagree, or not
    # have an assignment at all.
    def _lit_satisfied(self, lit): return self.assign.get(abs(lit)) == (lit > 0)
    def _lit_falsified(self, lit): return self.assign.get(abs(lit)) == (lit < 0)
    def _lit_unassigned(self, lit): return abs(lit) not in self.assign
    def _assign_lit_true(self, lit): self.assign[abs(lit)] = (lit > 0); del self.free[abs(lit)]

    def _assign_and_add_to_trail(self, lit, reason, level):
        self.agility *= G
        if lit > 0 != self.saved[abs(lit)]: self.agility += 1 - G
        self._assign_lit_true(lit)
        self.trail.append((lit, reason, level))
        self.level[abs(lit)] = level

    def _add_clause(self, c, watch1=None, watch2=None):
        c = list(set(c))
        if len(c) == 1:
            self.units.add(c[0])
            return None
        x = watch1 or c[0]
        y = (watch2 or c[0]) if (watch1 and x != c[0]) else (watch2 or c[1])
        clause = Clause(c, x, y)
        self.clauses.append(clause)
        self.watch[x].add(clause)
        self.watch[y].add(clause)
        return clause

    def _prune_lemmas(self):
        self.max_clauses += 300
        trail_clauses = set(reason for lit, reason, level in self.trail if reason is not None)
        num_to_keep = ((len(self.clauses) - self.first_learned) // 2) - len(trail_clauses)
        best_clauses = sorted(((c, len(c.lits)) for c in self.clauses[self.first_learned:] if c not in trail_clauses), key=lambda x: x[-1])[:num_to_keep]
        for clause in self.clauses[self.first_learned:]:
            for w in clause.watches:
                self.watch[w].remove(clause)
        self.clauses = self.clauses[:self.first_learned]
        for clause in itertools.chain(trail_clauses, (x[0] for x in best_clauses)):
            w1, w2 = clause.watches
            self._add_clause(clause.lits, w1, w2)

    def _backjump(self, backjump_level):
        while self.trail:
            lit, reason, level = self.trail[-1]
            if LOG > 1: print('  pop {}'.format((lit,reason,level)))
            if level <= backjump_level: return
            self.saved[abs(lit)] = lit > 0
            del self.assign[abs(lit)]
            del self.level[abs(lit)]
            self.free[abs(lit)] = True
            self.trail.pop()

    def solve(self, nvars, clauses):
        # Every variable should be in either assign (mapped to its current assignment) or in free,
        # but never in both. free is a dict so that we can test membership efficiently and use
        # popitem as a rough proxy for VSIDS, since popitem always returns the most recently added.
        self.assign = {} # var -> True/False
        self.free = {i: True for i in range(1, nvars+1)}
        self.level = {} # var -> level in the trail
        self.agility = 1.0  # When this gets too low, we should restart.
        self.saved = dict((v, False) for v in range(1,nvars+1))  # Saved recent values of vars.
        self.units = set()  # All unit clauses, stored as literals.
        self.watch = dict(((x, set()) for x in range(-nvars,nvars+1) if x != 0))  # Watchlists
        self.clauses = []  # The clause database.
        for clause in clauses:
            if not clause: return False
            assert max(abs(x) for x in clause) <= nvars
            self._add_clause(clause)
        self.max_clauses = len(self.clauses) * 2  # The max clauses we'll learn before pruning.
        self.first_learned = len(self.clauses)  # Index of the first learned clause, for pruning.
        self.trail = [(l, None, 0) for l in self.units]  # Tuples of (lit, reason, level).
        self.tp = 0  # Next unprocessed trail item.
        # Units aren't on watchlists, so we need to handle any initial conflicts first.
        for unit in self.units:
            if self._lit_falsified(unit): return False  # Conflicting units
            self._assign_lit_true(unit)

        current_level = 0
        while len(self.assign) < nvars or self.tp < len(self.trail):
            if len(self.clauses) > self.max_clauses: self._prune_lemmas()
            if LOG > 1: print('assignments: {}'.format(self.assign))
            # Propagate pending implications
            while self.tp < len(self.trail):
                wl, reason, _ = self.trail[self.tp]
                if LOG > 1: print('Propagating {} (reason: {})'.format(wl, reason))
                if LOG > 1: print('Trail: {}'.format(self.trail))
                self.level[abs(wl)] = current_level
                for clause in self.watch[-wl].copy():
                    if self._lit_satisfied(clause.other_watch(-wl)): continue
                    if LOG > 1: print('  Finding another watch for {}'.format(clause))
                    if LOG > 1:
                        print('    assignments: {}'.format(dict([abs(l), self.assign.get(abs(l))] for l in clause.lits)))
                    for l in clause.lits:
                        if l in clause.watches: continue
                        if self._lit_unassigned(l) or self._lit_satisfied(l):
                            if LOG > 1: print('    watching {} instead'.format(l))
                            clause.watches.remove(-wl)
                            clause.watches.add(l)
                            self.watch[-wl].remove(clause)
                            self.watch[l].add(clause)
                            break
                    # Did we fail in finding another watch?
                    if -wl in clause.watches:
                        forced = clause.other_watch(-wl)
                        if self._lit_falsified(forced):
                            if LOG > 1: print('Conflict with lit {}, clause {} and trail: {}. Resolving...'.format(forced, clause, self.trail))
                            if current_level == 0: return False  # UNSAT
                            stamp = dict((-l, True) for l in clause.lits)
                            if LOG > 1: print('stamped: {}'.format(stamp))
                            resolved = set(clause.lits)
                            current_level_lits = set(l for l in resolved if self.level[abs(l)] == current_level)
                            backjump_level, backjump_lit = current_level, None
                            # Resolve a conflict
                            for tl, tc, tlev in reversed(self.trail):
                                if tc is None: continue  # Decision
                                if stamp.get(tl):
                                    if LOG > 1: print('   resolving with {} on level {} since {} is stamped'.format(tc, tlev, tl))
                                    for l in tc.lits:
                                        if l != tl: stamp[-l] = True
                                        if -l in resolved:
                                            if self.level[abs(l)] == current_level: current_level_lits.remove(-l)
                                            resolved.remove(-l)
                                        else:
                                            if self.level[abs(l)] == current_level: current_level_lits.add(l)
                                            resolved.add(l)
                                    if len(current_level_lits) == 1:
                                        backjump_level, backjump_lit = 0, None
                                        for l in resolved:
                                            if backjump_level < self.level[abs(l)] < current_level:
                                                backjump_level, backjump_lit = self.level[abs(l)], l
                                        break
                            decision_lit, = current_level_lits
                            self._backjump(backjump_level)
                            self.tp = len(self.trail) - 1  # We'll inc again at end of this loop
                            resolved_clause = self._add_clause(resolved, decision_lit, backjump_lit)
                            #print('learned {}'.format(resolved_clause))
                            self._assign_and_add_to_trail(decision_lit, resolved_clause, backjump_level)
                            current_level = backjump_level
                            break
                        elif not self._lit_satisfied(forced):
                            if LOG > 1: print('  {} forced by {}, adding to trail and assigning'.format(forced, clause.lits))
                            self._assign_and_add_to_trail(forced, clause, current_level)
                if LOG > 1: print('  Done exploring watch list for {}'.format(-wl))
                self.tp += 1

            if len(self.assign) == nvars: break

            # If we haven't been selecting many new values for variables, we're probably stuck in a
            # rut and should restart, wiping out variable assignments but keeping learned clauses.
            if self.agility < 0.20:
                self._backjump(0)
                self.tp = len(self.trail)
                self.agility = 1.0

            # Nothing left to propagate. Make a decision and assignment then start a new level.
            v = self.free.popitem()[0]
            if LOG > 1: print('Trail: {}'.format(self.trail))
            self.assign[v] = self.saved[v]
            if LOG > 1: print('Choosing {} = {}'.format(v, self.assign[v]))
            current_level += 1
            self.level[v] = current_level
            self.trail.append(((1 if self.assign[v] else -1) * v, None, current_level))

        return [l * (1 if v else -1) for l, v in sorted(self.assign.items())]

def parse_dimacs(s):
    header, clauses, max_var, carryover = None, [], 0, []
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
    if assignments := Solver().solve(num_vars, clauses):
        stride = 10
        for i in range(0, len(assignments), stride):
            end = ' 0' if i + stride >= len(assignments) else ''
            print('v {}{}'.format(' '.join((str(x) for x in assignments[i:i+stride])), end))
        print('s SATISFIABLE')
        sys.exit(10)
    else:
        print('s UNSATISFIABLE')
        sys.exit(20)
