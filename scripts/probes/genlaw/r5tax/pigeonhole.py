#!/usr/bin/env python3
"""Lemma E-par (axis-parity pigeonhole): in the phi-frame, doubles live on EVEN
axes (2u mod 16), products on axis-parity u_i+u_j, Lambda on axis 8-pi (parity pi).
With w = #odd u_i: even-axis load EL = 5 + C(w,2) + C(5-w,2) + (1-pi) over 8 even
axes => even-axis collision excess >= EL - 8 >= 1 + (1-pi) for w in {2,3},
>= 3 + (1-pi) for w in {1,4}, >= 7 + (1-pi) for w in {0,5}.
Verify against all feasible classes."""
from collections import Counter, defaultdict
from itertools import combinations
import json

CL = json.load(open('/tmp/r5tax/classes.json'))
viol = 0
whist = Counter(); exhist = Counter()
for c in CL:
    pi, U = c['pi'], c['U']
    w = sum(u & 1 for u in U)
    lam = 8 - pi
    # even-axis occupancy
    occ = Counter()
    for u in U: occ[(2 * u) % 16] += 1
    for i, j in combinations(range(5), 2):
        a = (U[i] + U[j]) % 16
        if a % 2 == 0: occ[a] += 1
    if lam % 2 == 0: occ[lam] += 1
    EL = sum(occ.values())
    excess = sum(v - 1 for v in occ.values())
    bound = EL - 8
    whist[(pi, w)] += 1
    exhist[(pi, excess)] += 1
    # predicted load
    predEL = 5 + (w*(w-1)//2) + ((5-w)*(4-w)//2) + (1 - pi)
    assert EL == predEL, (pi, U, EL, predEL)
    if excess < max(bound, 0): viol += 1
    # the theorem-form bound: excess >= 1 + (1-pi) given w in {2,3}
print("w histogram (pi,w):", dict(sorted(whist.items())))
print("even-axis excess histogram (pi,excess):", dict(sorted(exhist.items())))
print("violations of excess >= EL-8:", viol)
mn = {p: min(e for (pp, e) in exhist if pp == p) for p in (0, 1)}
print("min even-axis excess: pi=0:", mn[0], " pi=1:", mn[1])
assert viol == 0
# corollary check: no feasible class with w in {0,5}? and lone-event nodes
print("classes with w in {0,5}:", sum(v for (p, w), v in whist.items() if w in (0, 5)))
print("classes with w in {1,4}:", sum(v for (p, w), v in whist.items() if w in (1, 4)))
# single-event classes (X+F totals): events = multi-axes count
single = [c for c in CL if len(c['node'][2]) + (0 if c['node'][1] == '|L' else 1) <= 1]
print("classes with <= 1 collision axis total:", len(single))
for c in single[:5]: print("  example:", c['node'])
