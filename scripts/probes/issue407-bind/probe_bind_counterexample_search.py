#!/usr/bin/env python3
"""RIGOROUS independent verification of a (BIND) counterexample.
Build a non-antipodal S subset {0..n-1} directly, find a thin prize prime p (p>n^3, n|p-1) with
Sum_{i in S} omega^i == 0 mod p, and CHECK all conditions independently (no reuse of the search code).
Three checks: (1) S non-antipodal, (2) Sum omega^i == 0 in F_p exactly, (3) p thin (p>n^3) and n|(p-1).
Also confirm the integer norm N = Res(x^{n/2}+1, c(x)) is divisible by p (the bridge), and |N|>... irrelevant.
"""
import sympy as sp
from sympy import Poly, resultant, symbols, factorint, isprime, primitive_root, gcd
x=symbols('x')

def reduced_from_S(n,S):
    m=n//2; c=[0]*m
    Ss=set(S)
    for j in range(m):
        a = 1 if j in Ss else 0
        b = 1 if (j+m) in Ss else 0
        c[j]=a-b
    return c

def is_antipodal(n,S):
    m=n//2; Ss=set(S)
    return all(((i+m)%n) in Ss for i in S)

def exact_norm_from_c(m,c):
    beta=Poly(sum(int(c[j])*x**j for j in range(m)), x, domain='ZZ')
    if beta.is_zero: return 0
    phi=Poly(x**m+1, x, domain='ZZ')
    return abs(int(resultant(phi,beta)))

def check_vanish_mod_p(n,S,p):
    g=primitive_root(p); w=pow(g,(p-1)//n,p)
    # verify w is a primitive n-th root
    assert pow(w,n,p)==1 and all(pow(w,n//q,p)!=1 for q in sp.primefactors(n))
    val=sum(pow(w,i,p) for i in S)%p
    return val, w

import random
random.seed(123)
for n in [32,64]:
    m=n//2
    print(f"\n=== n={n} verification ===",flush=True)
    found=False
    for attempt in range(400):
        # random non-antipodal S: choose for each j in 0..m-1 one of {none, j, j+m, both}, ensure not antipodal & nonzero c
        S=[]
        for j in range(m):
            r=random.random()
            if r<0.4: pass
            elif r<0.7: S.append(j)
            elif r<0.95: S.append(j+m)
            else: S+= [j, j+m]
        if not S: continue
        if is_antipodal(n,S): continue
        c=reduced_from_S(n,S)
        if not any(c): continue  # antipodal in disguise
        N=exact_norm_from_c(m,c)
        if N==0: continue
        fac=factorint(N, limit=2*10**6)
        cof=N
        for p,e in fac.items(): cof//=p**e
        primes=[p for p in fac if p>n**3 and (p-1)%n==0 and isprime(p)]
        if cof>1 and cof>n**3 and (cof-1)%n==0 and isprime(cof): primes.append(cof)
        for p in primes:
            val,w=check_vanish_mod_p(n,S,p)
            anti=is_antipodal(n,S)
            print(f"  CANDIDATE S (#S={len(S)}), p={p}:", flush=True)
            print(f"    [check1] non-antipodal: {not anti}", flush=True)
            print(f"    [check2] Sum omega^i mod p = {val}  (==0 required): {val==0}", flush=True)
            print(f"    [check3] p>n^3 ({p}>{n**3}): {p>n**3};  n|p-1: {(p-1)%n==0};  beta=log_n p={sp.log(p,n).evalf():.2f}", flush=True)
            print(f"    [bridge] p | N (N~2^{float(sp.log(N,2)):.1f}): {N%p==0}", flush=True)
            if (not anti) and val==0 and p>n**3 and (p-1)%n==0:
                print(f"    >>> CONFIRMED (BIND) COUNTEREXAMPLE at n={n}, p={p}. S={sorted(S)}", flush=True)
                found=True
                break
        if found: break
    if not found:
        print(f"  no confirmed counterexample at n={n} in 400 attempts", flush=True)
