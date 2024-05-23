#!/usr/bin/env python3

import argparse
import re

def parse_dimacs(s):
    header = None
    clauses = []
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
