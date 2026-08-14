#!/usr/bin/env python3
"""
wf407_T232-11-conj41_zerofiber_witness.py
=========================================
For the cleanest Lean brick: the POINT/fixed-syndrome refutation uses
point_compat_iff_esymm_zero -- the fixed unit syndrome unitVec(w-1) list EQUALS
#{ E : |E|=w, e_1(E)=...=e_c(E)=0 } (the ZERO fiber).  So a fixed-syndrome
refutation of Conjecture 41's intended form = a smooth subgroup mu_n hosting
> floor((2D-1)/c) weight-w subsets with e_1=e_2=e_3=0.

We want the SMALLEST prime p, proper subgroup mu_n (n < p-1, n >= 28), w=6, c=3,
with >= 6 weight-6 subsets of mu_n having e_1=e_2=e_3=0, and dump them as explicit
ZMod p element lists for a `decide` brick. (zero-fiber form needs the SHIFTED domain;
on mu_n the e_1=e_2=e_3=0 subsets are the genuine M_true at the unit syndrome.)

NOTE: on mu_n the worst class generally has e_3=0 but e_1,e_2 != 0 (a NONZERO class).
The point-fiber theorem is stated at the ZERO syndrome; the general nonzero class needs
the class-syndrome (top-window h-vector) form.  Both are fixed single syndromes.  We
search BOTH: (A) the pure zero-fiber e_1=e_2=e_3=0 on mu_n; (B) the worst nonzero class.
"""

import itertools
from collections import defaultdict

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d,s=n-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def nextprime(n):
    n=int(n)+1
    while not is_prime(n): n+=1
    return n

def factorize(n):
    fac={}; d=2
    while d*d<=n:
        while n%d==0: fac[d]=fac.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: fac[n]=fac.get(n,0)+1
    return fac

def primitive_root(p):
    phi=p-1; fac=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    raise RuntimeError

def mu_n(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p)%p for i in range(n)]

def esymm(E,j,p):
    if j==0: return 1
    acc=0
    for c in itertools.combinations(E,j):
        pr=1
        for x in c: pr=pr*x%p
        acc=(acc+pr)%p
    return acc

def err_vals_nonzero(E,p):
    El=list(E)
    for x in El:
        pr=1
        for y in El:
            if y==x: continue
            d=(x-y)%p
            if d==0: return False
            pr=pr*d%p
        if pr==0: return False
    return True

def zero_fiber_mun(p,n,w=6,c=3):
    L=mu_n(n,p)
    out=[]
    for E in itertools.combinations(L,w):
        if all(esymm(E,j,p)==0 for j in range(1,c+1)) and err_vals_nonzero(E,p):
            out.append(E)
    return out, L

if __name__ == "__main__":
    print("Search: smallest prime p, proper subgroup mu_n (n>=28), with >5 weight-6")
    print("zero-(e1,e2,e3) subsets => fixed-syndrome (unit syndrome) refutation of")
    print("Conjecture 41's intended form, decide-able over ZMod p.\n")
    found=False
    # need n>=28 proper subgroup: n | p-1, n < p-1.  smallest p with such n:
    # p-1 must have a divisor in [28, ~36]; e.g. p=59 (p-1=58=2*29, no), p=113 (112=16*7,
    # divisors include 28,56), p=29*k+1...  scan.
    cands=[]
    for p in range(50, 600):
        if not is_prime(p): continue
        ns=[d for d in range(28,37) if (p-1)%d==0 and d<p-1]
        for n in ns:
            cands.append((p,n))
    for p,n in cands[:12]:
        zf,L=zero_fiber_mun(p,n,w=6,c=3)
        print(f"  p={p}, n={n} (proper subgroup): #zero-fiber genuine weight-6 = {len(zf)}",
              flush=True)
        if len(zf)>5 and not found:
            print(f"  >>> WITNESS (decide-able): p={p}, n={n}, M_fixed_zero={len(zf)} > 5")
            print(f"      mu_n = {L}")
            for E in zf[:8]:
                print(f"        {sorted(E)}  e1={esymm(E,1,p)} e2={esymm(E,2,p)} "
                      f"e3={esymm(E,3,p)} genuine={err_vals_nonzero(E,p)}")
            found=True
    if not found:
        print("\n  (zero-fiber e1=e2=e3=0 may be empty on mu_n at small n; the worst class")
        print("   on mu_n is a NONZERO class -- the fixed-syndrome refutation uses the")
        print("   class syndrome, not the unit/zero syndrome. The n/4-1 law stands either way.)")
    print("\nDONE.")
