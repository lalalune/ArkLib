#!/usr/bin/env python3
# wf-M2 PRE-SCREEN II: the DECISIVE depth-R>=2 question via MITM.
#
# The depth-Stickelberger sufficient lemma gives  p <= w^{n/(4R)}  for a GENUINE (non-char-0)
# config of size w vanishing at the first R odd power sums. The route closes the prize iff the
# ACTUAL largest genuine bad prime at the deep-moment depth R ~ beta ln n is << p = n^beta.
#
# This probe finds, by 3+3 / 2+2 meet-in-the-middle on (o_1, o_3) [depth R=2] and (o_1,o_3,o_5)
# [R=3], the LARGEST genuine bad prime for each n, and compares to the ceiling w^{n/(4R)} AND to
# the prize field n^beta. If max_bad grows like n^{Theta(log n)} (campaign claim) it BLOWS PAST
# both the ceiling-relevant regime and the field => the GENERIC prize prime is bad at depth 2,3.
#
# CONCLUSION TEMPLATE: if max_bad(R=2) >> n^2, the depth-2 char-p transfer is NOT free (the
# Stickelberger ceiling is non-vacuous only at R~n/8) -> the generic-prime route is DEAD; one
# must pivot to the SPECIFIC prize prime's splitting (which Stickelberger does NOT control
# without knowing p's actual cyclotomic-norm factorization). We REFUTE the generic route here.

import itertools
from collections import defaultdict
from sympy import primerange
from math import log

def prim_root_n(p, n):
    if (p-1)%n: return None
    e=(p-1)//n; H=n//2
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,H,p)==p-1: return g
    return None

def char0_o(idxs, n, j):
    # exact char-0 vanishing test for signed indicator on exponent multiset idxs (with signs)
    import cmath
    return sum(cmath.exp(2j*cmath.pi*a*j/n) for a in idxs)

def largest_bad_R2(n, hi, size_half=3):
    """Largest genuine bad prime: antipodal-free 2*size_half subset with o_1=o_3=0 mod p,
    NOT char-0 vanishing. MITM split size_half+size_half."""
    H=n//2; best=0; bestp=None
    for p in primerange(n+1, hi):
        if p%n!=1: continue
        g=prim_root_n(p,n)
        if g is None: continue
        pw1=[pow(g,j,p) for j in range(n)]
        pw3=[pow(g,(3*j)%n,p) for j in range(n)]
        half=defaultdict(list)
        rng=range(n)
        for combo in itertools.combinations(rng,size_half):
            if any((i+H)%n in combo for i in combo): continue
            key=(sum(pw1[t] for t in combo)%p, sum(pw3[t] for t in combo)%p)
            half[key].append(combo)
        found=False
        for key,lst in half.items():
            neg=((-key[0])%p,(-key[1])%p)
            if neg not in half: continue
            for c1 in lst:
                s1=set(c1)
                for c2 in half[neg]:
                    S=s1|set(c2)
                    if len(S)!=2*size_half: continue
                    if any((x+H)%n in S for x in S): continue
                    # genuine: char-0 o_1 and o_3 not both ~0 for this UNSIGNED subset
                    # (subset, all +1 signs). char-0 vanishing of all-+1 antipodal-free set:
                    o1=char0_o(list(S),n,1); o3=char0_o(list(S),n,3)
                    if abs(o1)>1e-6 or abs(o3)>1e-6:
                        found=True; break
                if found: break
            if found: break
        if found:
            if p>best: best=p; bestp=p
    return best

print("wf-M2 depth-2 ceiling pre-screen (largest GENUINE bad prime, o_1=o_3=0, size-6 MITM)\n")
print(f"{'n':>5} {'max_bad(R=2,w=6)':>18} {'ceil w^(n/8)=6^(n/8)':>22} {'n^4 (prize-ish)':>16} {'log_n(max)':>11}")
for n,hi in [(8,5000),(16,40000),(32,120000),(64,200000)]:
    mb=largest_bad_R2(n,hi,size_half=3)
    ceil=6**(n/8)
    n4=n**4
    ln_=log(mb)/log(n) if mb>0 else 0
    print(f"{n:>5} {mb:>18} {ceil:>22.3e} {n4:>16} {ln_:>11.3f}")
print("\nNOTE: w=6, R=2 => ceiling=6^(n/4R)=6^(n/8). If max_bad <= ceiling: lemma VALID.")
print("If max_bad >> n^4: GENERIC prize-prime route DEAD at depth 2 (must pin SPECIFIC prime).")
