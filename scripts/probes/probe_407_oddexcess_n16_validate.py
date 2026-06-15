#!/usr/bin/env python3
"""
Fast n=16 odd-excess validation + THINNESS test, restricted to the binding spike rung only.
E = I_n(x^{2a'}) - I_{n/2}(x^{a'}); in-tree n=16: spike at half-rung r'=5, E=64=(n/2)^2.
THINNESS (rule-3): same E at THIN (p~n^4) vs THICK (small proper p)?  thickness-monotone => dead.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import incidence

def isprime(m):
    if m<2: return False
    for d in range(2,int(m**0.5)+1):
        if m%d==0: return False
    return True
def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def subgroup(p,n):
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in prime_factors(n)):
            S=[pow(g,j,p) for j in range(n)]
            if len(set(S))==n: return S
    return None
def first_prime_index(n, m_lo):
    m=max(m_lo,2)
    while True:
        p=n*m+1
        if isprime(p): return p, m
        m+=1

def In_dir(S, p, K, r, b):
    """I for the fixed direction x^b at code degree K, rung r; max over offset a. saturate->p."""
    n=len(S); size=n-r
    if size<=K: return p
    if not (K <= b < size): return None  # not far
    best=-1
    for a in range(n):
        if a==b: continue
        c,sat=incidence(S,p,K,a,b,r)
        if sat: c=p
        if c>best: best=c
    return best

if __name__=='__main__':
    n=16; nh=8; k=2; K=2*k; a_half=k; a_even=2*a_half; target=nh*nh
    print(f"n={n} nh={nh} k={k} rho=1/4  half x^{a_half} deg {k}  even x^{a_even} deg {K}  target E=(n/2)^2={target}")
    primes_thin = [first_prime_index(n, n**3)[0]]
    primes_thick= [first_prime_index(n, 2)[0]]
    # only the binding-region rungs on the half domain
    rungs = [4,5,6]
    for label, plist in [("THIN p~n^4", primes_thin), ("THICK small p", primes_thick)]:
        print(f"\n--- {label} ---")
        for p in plist:
            m=(p-1)//n
            Sf=subgroup(p,n); Sh=subgroup(p,nh)
            print(f"  p={p} index_full={m} index_half={(p-1)//nh}  q/n={p/n:.1f}")
            for r in rungs:
                Ih = In_dir(Sh, p, k, r, a_half)
                In = In_dir(Sf, p, K, r, a_even)
                E = None if (Ih is None or In is None) else In-Ih
                mk = "  <== E=(n/2)^2" if (E==target) else ("  E>0" if (E and E>0) else "")
                print(f"      r'={r}: I_n/2={Ih}  I_n={In}  E={E}{mk}", flush=True)
