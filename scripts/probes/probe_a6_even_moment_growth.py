#!/usr/bin/env python3
"""
A6 DECISIVE TEST (vectorized) — growth of normalized even power sums.

c_k = mu_{2k}/n^k where mu_{2k} = (1/m) sum_i eta_i^{2k}.  The normalized period
measure nu = (1/m) sum delta_{eta_i/sqrt(n)} has even moments c_k.  Its L-infinity
norm = M/sqrt(n) = lim_k c_k^{1/2k}.

DECISION:
 * c_k^{1/2k} saturates to ABSOLUTE constant as p->inf (fixed n)  => M<=C sqrt(n) => CRACK
 * c_k^{1/2k} creeps up with p (log dependence)                   => M~sqrt(n log) => Johnson

Vectorized: build periods by bucketing the p-1 residues g^{i+m t} into their
period index i in [0,m).  All cos values computed via numpy.
"""
import math
import numpy as np
from sympy import isprime

def primitive_root(p):
    phi=p-1; fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def periods_real(p,n):
    """Vectorized: eta_i = sum over residues r with discrete-log(r) = i mod m, of cos(2pi r/p).
       discrete log base g: residue g^e has e; e = i + m*t, period index = e mod m.
       Build by walking the cyclic group: r_e = g^e for e=0..p-2, period idx = e % m."""
    m=(p-1)//n
    g=primitive_root(p)
    N=p-1
    # block discrete-power: e = a*B + b, g^e = g^{aB} * g^b (mod p).
    B=int(math.isqrt(N))+1
    low=np.empty(B,dtype=object)   # g^b mod p, b=0..B-1  (python ints to avoid overflow)
    cur=1
    for b in range(B):
        low[b]=cur; cur=cur*g%p
    gB=cur  # g^B
    A=(N+B-1)//B
    high=np.empty(A,dtype=object)
    cur=1
    for a in range(A):
        high[a]=cur; cur=cur*gB%p
    low=low.astype(object);
    eta=np.zeros(m)
    twopi_over_p=2.0*math.pi/p
    for a in range(A):
        hb=high[a]
        b0=a*B
        bcount=min(B,N-b0)
        if bcount<=0: break
        # residues for e=b0..b0+bcount-1
        # (hb * low[0:bcount]) % p  -- do in python int then to float
        res=(hb*low[:bcount])%p
        res=res.astype(np.float64)
        cosv=np.cos(twopi_over_p*res)
        idx=(np.arange(b0,b0+bcount)%m)
        np.add.at(eta,idx,cosv)
    return eta,m

def run(p,n,Kmax=8):
    eta,m=periods_real(p,n)
    M=float(np.max(np.abs(eta)))
    sn=math.sqrt(n)
    norm=eta/sn
    out=[]
    for k in range(1,Kmax+1):
        mom=float(np.mean(norm**(2*k)))   # c_k = E[ (eta/sqrt n)^{2k} ]
        Ln=mom**(1.0/(2*k))
        out.append(Ln)
    return M,sn,M/sn,out,m

def find_primes(n,count,pmin):
    res=[]; t=pmin//n+1
    while len(res)<count:
        p=1+n*t
        if isprime(p): res.append(p)
        t+=1
    return res

if __name__=="__main__":
    print("=== A6 DECISIVE: c_k^{1/2k} (L^{2k} norm of normalized period measure) ===")
    print("Prize regime: n FIXED, p -> infinity, all p >> n^3, p PRIME, proper subgroup.\n")
    Kmax=10
    for mu in [3,4,5,6]:
        n=2**mu
        # all p >> n^3; cap top decade so the cyclic-walk array stays <~ 4e8 entries
        base=[50,1000,20000,400000]
        decades=sorted(set( min(c*n**3, 4*10**7) for c in base ))
        print(f"########## n=2^{mu}={n}  sqrt(n)={math.sqrt(n):.3f} ##########")
        hdr=" ".join(f"L{2*k}".rjust(6) for k in range(1,Kmax+1))
        print(f"{'p':>13} {'p/n^3':>8} {'M/sqn':>7} | {hdr}")
        for pmin in decades:
            for p in find_primes(n,1,int(pmin)):
                M,sn,r,out,m=run(p,n,Kmax)
                row=" ".join(f"{x:6.3f}" for x in out)
                print(f"{p:>13} {p/n**3:8.0f} {r:7.3f} | {row}")
        print()
    print("READING: across a FIXED n block, if L^{2k} columns rise with p (and with")
    print("higher k), M carries log(p/n) -> Johnson.  If flat in p -> constant -> crack.")
