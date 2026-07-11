#!/usr/bin/env python3
"""
probe_407_crosscell_dcsub_form.py  (#407/#444: which crossCell upper bound is the RIGHT open form?)

Given that the POINTWISE absolute bound  crossCell*q <= 2^r * |H|^r  is REFUTED
(probe_407_crosscell_absolute_pointwise.py: violated for all r>=3, all primes),
test the DC-SUBTRACTED candidate forms to find the one that is NOT pointwise-refuted:

  (A) absolute (REFUTED):         crossCell*q <= 2^r * |H|^r
  (B) +random-main-term:          crossCell*q <= (2^r - 2) * |H|^r + Wick,  Wick=(2r-1)!! * |H|^r
  (C) just random-main-term:      crossCell*q <= (2^r - 2) * |H|^r
  (D) DC-only proxy:              crossCell    <= 2^r * |H|^r / q  (== A; same thing)

The #444 sec.2/sec.11 MANDATORY form is the DC-subtracted A_r = E_r - n^{2r}/q <= Wick.
Here we test the crossCell analogue (B) and (C) to see which holds pointwise at small
prize-shaped instances (so we land a TRUE statement, not just a refutation).

EXACT, multi-prime, PROPER mu_n (m=(p-1)/n>1), p==1 mod n, NEVER n=q-1.
"""
import math

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1; fac = factorize(phi)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac): return g
    raise RuntimeError

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def subgroup(p, n):
    assert (p-1)%n==0
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return sorted(set(S))

def circ_mul(a,b,p):
    out=[0]*p
    nzb=[(j,bj) for j,bj in enumerate(b) if bj]
    for i,ai in enumerate(a):
        if not ai: continue
        for j,bj in nzb: out[(i+j)%p]+=ai*bj
    return out

def N0_exact(S,r,p):
    f=[0]*p
    for x in S: f[x%p]+=1
    acc=[0]*p; acc[0]=1; base=f; e=r
    while e>0:
        if e&1: acc=circ_mul(acc,base,p)
        e>>=1
        if e: base=circ_mul(base,base,p)
    return acc[0]

def dfact(k):  # (2r-1)!! with k=2r-1
    r=1
    while k>0: r*=k; k-=2
    return r

def run():
    cases={8:[97,193,577,1153,2593], 16:[97,193,257,1153], 32:[193,257,577]}
    print("# crossCell upper-bound FORM selection (which holds pointwise?)")
    print("# B = (2^r-2)|H|^r + Wick ; C = (2^r-2)|H|^r ; cross*q compared")
    failB=False; failC=False
    for n in (8,16,32):
        Hn=n//2
        for p in cases[n]:
            if (p-1)%n!=0: continue
            m=(p-1)//n
            if m<2: continue
            G=subgroup(p,n); H=subgroup(p,Hn)
            rmax = 8 if n<32 else 6
            for r in range(2, rmax+1):
                N0G=N0_exact(G,r,p); N0H=N0_exact(H,r,p)
                cross=N0G-2*N0H
                lhs=cross*p
                Hr=Hn**r
                wick=dfact(2*r-1)*Hr
                B=(2**r-2)*Hr + wick
                C=(2**r-2)*Hr
                okB = lhs<=B; okC = lhs<=C
                if not okB: failB=True
                if not okC: failC=True
                if r in (3,4,6,rmax):
                    print(f"n={n:2d} p={p:5d} r={r:2d} cross*q={lhs:14d} "
                          f"C={C:14d} {'okC' if okC else 'FAILC':5s}  "
                          f"B={B:14d} {'okB' if okB else 'FAILB':5s}")
    print()
    print(f"FORM C (2^r-2)|H|^r  pointwise: {'REFUTED' if failC else 'HOLDS in tested range'}")
    print(f"FORM B  +Wick        pointwise: {'REFUTED' if failB else 'HOLDS in tested range'}")

if __name__=='__main__':
    run()
