# probe_ak_wick_direct.py  (#444, AK_LE_WICK_DIRECT angle)
# Direct sweep of the RE-POINTED open kernel A_K <= Wick_K = (2K-1)!! n^K (NOT the dead A_K<=E_K^C).
# A_K = N_K - n^{2K}/p, N_K = sum_s c_K(s)^2 (exact int K-fold cyclic convolution of mu_n indicator).
# Whole-window worst-case (incl bad primes). FINDING: max A_K/Wick at K=1 (=1-n/p), decreasing in K;
# NO violation across n=8 (115 primes) and n=16 (691 primes incl bad p=76001). Binding pt = provable K=1.
# Companion Lean brick: ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvAK_WickDirect.lean
# AK_LE_WICK_DIRECT probe (#444). Target: A_K <= Wick_K = (2K-1)!! n^K.
# A_K = N_K - n^{2K}/p, N_K = additive 2K-energy of mu_n = sum_s c_K(s)^2.
# REUSE exact integer convolution. Sweep WHOLE window incl bad primes.
import numpy as np
from fractions import Fraction as Fr
from math import log

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: ok=True; break
        if not ok: return False
    return True

def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

def subgroup(p,n):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=x*w%p
    return S

def doublefact_odd(k):
    r=1
    for i in range(1,k+1): r*=(2*i-1)
    return r

def Ncounts(p,roots,Kmax):
    c=np.zeros(p,dtype=np.int64)
    for r in roots: c[r]+=1
    rolls=roots
    Ns=[]
    for K in range(1,Kmax+1):
        Ns.append(sum(int(v)*int(v) for v in c.tolist()))
        if K<Kmax:
            acc=np.zeros(p,dtype=np.int64)
            for r in rolls:
                acc+=np.roll(c,r)
            if acc.max()>9_000_000_000_000_000_000:
                raise OverflowError(f"int64 overflow at K={K+1}")
            c=acc
    return Ns

def v2(x):
    k=0
    while x%2==0: x//=2; k+=1
    return k

# window sweep for n=8 and n=16: A_K/Wick directly, worst-case over primes
for n in (8,16):
    lo=n**4; hi=2*n**4
    primes=[p for p in range(lo,hi) if (p-1)%n==0 and is_prime(p)]
    print(f"\n=== n={n}, window [{lo},{hi}), {len(primes)} primes p=1 mod n ===")
    Kmax = int(log(hi))+1
    # track worst (max) A_K/Wick per K across all primes
    worst_ratio = {K:(-1.0,None) for K in range(1,Kmax+1)}
    any_violation=False
    for p in primes:
        roots=subgroup(p,n)
        Ns=Ncounts(p,roots,Kmax)
        for K in range(1,Kmax+1):
            NK=Ns[K-1]
            AK=Fr(NK)-Fr(n**(2*K),p)
            Wick=Fr(doublefact_odd(K)*n**K)
            r=float(AK/Wick)
            if r>worst_ratio[K][0]:
                worst_ratio[K]=(r,p)
            if AK>Wick:
                any_violation=True
                print(f"  *** VIOLATION A_K>Wick at p={p} K={K}: A={float(AK):.3e} Wick={float(Wick):.3e} ratio={r:.4f}")
    print(f"  worst A_K/Wick per K (must be <=1):")
    for K in range(1,Kmax+1):
        r,p=worst_ratio[K]
        print(f"    K={K:2d}: max A_K/Wick = {r:.5f} @p={p} (v2(p-1)={v2(p-1)})")
    print(f"  any A_K>Wick violation in window? {any_violation}")
