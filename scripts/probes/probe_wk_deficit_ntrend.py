# probe_wk_deficit_ntrend.py  (#444, char-p kernel ground truth)
# Independently reproduces W_K = A_K - E_K^C < 0 (the open-kernel sign) by EXACT integer
# convolution: A_K = N_K - n^{2K}/p, N_K = sum_s c_K(s)^2, c_K = K-fold cyclic conv of the
# mu_n indicator mod p; E_K^C = besselE K (n/2) exact rational; Wick_K=(2K-1)!! n^K.
# FINDING (2026-06-19): W_K<0 across n=8 (19 primes p~8^4), n=16 (p=65617), n=32 (p=1048609),
#   full K-range to floor(log p). Small-K edges are provably-negative Parseval trivia
#   (W_1=-n^2/p exact; E_2^C=3n^2-3n, W_2~=-1 absolute). The DEEP-K bulk deficit (barrier
#   regime K~log p) DEEPENS with n in normalized terms: max |W_K/Wick| = 0.94%/2.68%/2.86%
#   for n=8/16/32. Nearly p-independent at fixed (n,K). Reassures W_K<=0; does NOT settle the
#   asymptotic n->2^30 (the open kernel; finite computation cannot reach it).

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

def besselE(K,m):
    fact=[1]*(K+1)
    for i in range(1,K+1): fact[i]=fact[i-1]*i
    base=[Fr(1,fact[j]*fact[j]) for j in range(K+1)]
    poly=[Fr(0)]*(K+1); poly[0]=Fr(1)
    for _ in range(m):
        new=[Fr(0)]*(K+1)
        for a in range(K+1):
            if poly[a]==0: continue
            pa=poly[a]
            for b in range(K+1-a):
                new[a+b]+=pa*base[b]
        poly=new
    f2K=1
    for i in range(1,2*K+1): f2K*=i
    return poly[K]*f2K

def Ncounts(p,roots,Kmax):
    # numpy int64 convolution (exact while values < 9.2e18), N_K via python bigint sum of squares
    c=np.zeros(p,dtype=np.int64)
    for r in roots: c[r]+=1
    rolls=roots
    Ns=[]
    for K in range(1,Kmax+1):
        # N_K = sum c^2 (python bigint to avoid overflow)
        Ns.append(sum(int(v)*int(v) for v in c.tolist()))
        if K<Kmax:
            acc=np.zeros(p,dtype=np.int64)
            for r in rolls:
                acc+=np.roll(c,r)
            # overflow guard
            if acc.max()>9_000_000_000_000_000_000:
                raise OverflowError(f"int64 overflow at K={K+1}")
            c=acc
    return Ns

def run(n, p, Kmax=None):
    m=n//2
    roots=subgroup(p,n)
    Km=Kmax or (int(log(p))+1)
    Ns=Ncounts(p,roots,Km)
    worst=None; worstK=None; rows=[]
    for K in range(1,Km+1):
        NK=Ns[K-1]
        AK=Fr(NK)-Fr(n**(2*K),p)
        EC=besselE(K,m)
        WK=AK-EC
        Wick=Fr(doublefact_odd(K)*n**K)
        normW=float(WK/Wick)      # W_K / Wick_K  (negative; closest-to-0 = worst)
        rows.append((K,float(WK),normW, float(AK/EC)))
        if worst is None or normW>worst: worst=normW; worstK=K
    return Km,worst,worstK,rows

print("n  |  p          | Kmax | worst W_K/Wick (closest to crossing, <0=safe) @K | A_K<=E_C all K?")
print("-"*92)
cases=[(8,4129),(16,65617),(32,1048609)]
trend=[]
for n,p in cases:
    assert (p-1)%n==0 and is_prime(p), (n,p)
    Km,worst,wK,rows=run(n,p)
    allle = all(r[1]<0 for r in rows)
    trend.append((n,worst))
    print(f"{n:3d}| {p:10d} | {Km:4d} | {worst:+.5f} @K={wK:2d}                              | {allle}")
    # show per-K normalized deficit
    s=' '.join(f'{r[2]:+.4f}' for r in rows)
    print(f"     W_K/Wick per K: {s}")
print("\nMARGIN TREND (worst |W_K/Wick| as n grows 8->16->32):")
for n,w in trend: print(f"  n={n:3d}: worst W_K/Wick = {w:+.5f}  (|margin|={abs(w):.5f})")
print("\nINTERPRETATION: if |margin| stays bounded away from 0 (or grows), the deficit persists;")
print("if it shrinks toward 0 with n, that flags a possible asymptotic crossing.")
