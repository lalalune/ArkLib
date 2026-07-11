#!/usr/bin/env python3
"""
Probe a CLEAN closed-form hypothesis-free lower bound on rEnergy(G,r) that STRICTLY
beats the diagonal floor |G|^r for r >= 2.

Candidate: DIAGONAL union SINGLE-TRANSPOSITION-(0,1) family.
  Diagonal D  = {(v,v)}                         (|D| = n^r)
  Swap01   S  = {(v,w): w = v with coords 0,1 swapped}  (|S| = n^r)
  Both have sum w = sum v, so D, S subset of energySet.
  Overlap D cap S = {v : v_0 = v_1} (then swap = identity) => |D cap S| = n^{r-1} * n? 
    v_0=v_1 free, other r-2 coords free => n * n^{r-2} = n^{r-1}.  (choose v_0=v_1: n ways; rest n^{r-2})
  |D union S| = 2 n^r - n^{r-1}.

So conjecture:  rEnergy(G,r) >= 2 n^r - n^{r-1}  for all r>=2, hypothesis-free, char-free
(NO negation-closure needed - swap is a pure permutation symmetry).
At r=2: 2n^2 - n  (matches E2CharFree T1 cup T2). 
"""
import itertools
from collections import Counter

def rEnergy(G, r):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v)] += 1
    return sum(c*c for c in cnt.values())

def diag_union_swap01(G, r):
    # count distinct pairs (v,w) with w=v OR w=swap01(v)
    n = len(G)
    seen = set()
    for v in itertools.product(G, repeat=r):
        seen.add((v, v))
        if r >= 2:
            w = (v[1], v[0]) + v[2:]
            seen.add((v, w))
    return len(seen)

if __name__ == "__main__":
    print("n  r | 2n^r - n^{r-1}  diagUnionSwap(brute)  rEnergy | floor<=rEnergy?  formula==brute?")
    for n in [2,3,4,5]:
        G = list(range(n))
        for r in [2,3,4,5]:
            formula = 2*n**r - n**(r-1)
            brute = diag_union_swap01(G, r)
            re = rEnergy(G, r)
            print(f"{n}  {r} | {formula:8d}  {brute:8d}  {re:8d} | {formula<=re}  {formula==brute}")
