#!/usr/bin/env python3
"""
TRUE-CORE B vs budget — THINNESS test across beta (#444).

Companion to probe_407_truecore_B_vs_budget.py (0xSolace ed1db3379, which showed B=max_stack
#distinct-bad-gamma is WITHIN the eps* budget at every finite r, ratio 0.04-0.41x, at beta=4.0/4.5
[both THIN/prize-shape]). That probe did NOT test the THICK regime. THIS one sweeps beta from THICK
(beta~2.3, prize-FALSE) to THIN (beta~5, prize-shape) and reads B and B/budget at the binding rung.

QUESTION (rule-3): is the B-feasibility margin (B/budget = 0.04-0.41) THINNESS-ESSENTIAL?
  (A) B/budget grows toward 1 as mu_n thickens (beta down) => the feasibility margin IS thin content
      => a POSITIVE thin-direction result (rare on this board).
  (B) B/budget is thickness-invariant => B feasibility is Johnson-margin, not thin-specific.

Reuses the sibling's EXACT engine (nbad_at_band, charline, find_g, next_prime_cong1) verbatim.
Exact mod-p, PROPER mu_n (m>1, never n=q-1).
"""
import sys, math, itertools, random
sys.path.insert(0, 'scripts/probes')
from probe_407_truecore_B_vs_budget import (next_prime_cong1, find_g, nbad_at_band,
                                            charline, is_prime)

def maxB_n16(xs, p, kdim, a, n, lines):
    B=0; arg=None
    for (A,Bb) in lines:
        if A>=n or A==Bb: continue
        u0,u1=charline(A,Bb,xs,p)
        c=nbad_at_band(u0,u1,xs,p,kdim,a)
        if c>B: B=c; arg=(A,Bb)
    rng=random.Random(999^p)
    for _ in range(6):
        ru0=[rng.randrange(p) for _ in range(n)]; ru1=[rng.randrange(p) for _ in range(n)]
        c=nbad_at_band(ru0,ru1,xs,p,kdim,a)
        if c>B: B=c; arg=('rand',)
    return B,arg

if __name__=='__main__':
    print("="*88)
    print("TRUE-CORE B vs eps* budget, THINNESS sweep across beta (THICK prize-FALSE -> THIN prize-shape)")
    print("B = max_stack #distinct-bad-gamma; budget = 2^r*C(2^{mu-1},r); ratio = B/budget")
    print("="*88)
    n=16; mu=4
    n16_lines=[(9,7),(10,8),(9,8),(8,4),(15,13),(10,6),(12,8),(8,6),(7,5),(6,4),(11,9),(14,10)]
    # binding rung for n=16 prize shape: the sibling found feasibility at all r; we read r=4 (a known
    # census-overflow band) + r=8 (Johnson band) to compare thin vs thick at the SAME bands.
    for beta in (2.3, 2.6, 3.0, 3.5, 4.0, 5.0):
        p=next_prime_cong1(n, int(n**beta))
        fermat = bin(p-1).count('1')==1
        g=find_g(p,n); xs=[pow(g,i,p) for i in range(n)]
        print(f"\n--- n={n} beta={beta} p={p} idx={(p-1)//n} {'[Fermat]' if fermat else '[non-Fermat]'} ---")
        for r in (4, 8):
            kdim=r-1; a=r+1
            if a>n or r>2**(mu-1): continue
            budget=(2**r)*math.comb(2**(mu-1),r)
            B,arg=maxB_n16(xs,p,kdim,a,n,n16_lines)
            v="FEASIBLE" if B<=budget else "*** B>budget ***"
            print(f"  r={r} k={kdim} a={a}: B={B} (worst={arg}) budget={budget} "
                  f"ratio={B/budget:.4f} {v}", flush=True)
