#!/usr/bin/env python3
# wf-G2 (#444): HONEST resonance lower bound, FIXED beta (no shrinking-log artifact).
#
# Three quantities per (n, FIXED beta):
#   truemax  = max_c |eta_c|            (brute, over scanned cosets)
#   resLB    = BEST data-INDEPENDENT coset-subgroup resonator LB
#              = max_{d|m} |sum_{c in H_d} eta_c| / |H_d|   (full scan only)
#   floor    = sqrt(n ln(p/n))
# Report resLB/floor and truemax/floor vs n at FIXED beta. The resonance method's claim
# is that resLB grows; if resLB/floor is FLAT and resLB << truemax, the multiplicative
# resonator FAILS to certify a large period (periods are coset-decorrelated) => no Omega
# growth from this construction => floor is tight (prize plausible).

import math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if x % q == 0: return x == q
    d=x-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in (1,x-1): continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True

def factor(x):
    f=[]; d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: f.append(x)
    return f

def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g

def find_prime_near(n, beta):
    target=int(n**beta); k=max(2,(target-1)//n)
    while True:
        p=1+k*n
        if p>=target and isprime(p) and (p-1)//n>1: return p
        k+=1

def periods(p, n, m_cap):
    g=proot(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,j,p) for j in range(n)], dtype=np.int64)
    w=2*math.pi/p
    M=min(m,m_cap)
    per=np.empty(M,dtype=np.float64)
    rep=1
    for c in range(M):
        per[c]=np.cos(w*((rep*mu)%p)).sum()
        rep=(rep*g)%p
    return per, m, M

def subgroup_reslb(per, m, M):
    if M!=m: return None, None
    best=0.0; lab=None
    d=1; ds=[]
    while d<=m:
        if m%d==0: ds.append(d)
        d+=1
    for dord in ds:
        if dord==1: continue   # exclude trivial single-element subgroup (that is 'single')
        step=m//dord
        idx=(step*np.arange(dord))%m
        lb=abs(per[idx].sum())/dord
        if lb>best: best=lb; lab=dord
    return best, lab

if __name__=="__main__":
    BETA=float(sys.argv[1]) if len(sys.argv)>1 else 4.0
    m_cap=int(sys.argv[2]) if len(sys.argv)>2 else 300000
    print(f"FIXED beta={BETA}, m_cap={m_cap}.  resLB = best NON-trivial subgroup resonator (data-independent).")
    print(f"{'n':>5} {'p':>11} {'m':>9} {'full?':>5} {'truemax':>9} {'subResLB':>9} {'floor':>9} {'true/flr':>9} {'subRes/flr':>11} {'subRes/true':>11}")
    rows=[]
    for mu in range(3,11):
        n=2**mu
        p=find_prime_near(n,BETA)
        m=(p-1)//n
        if m>m_cap and m>5_000_000:    # too big even to scan; stop
            break
        per,m,M=periods(p,n,min(m_cap,m))
        full=(M==m)
        truemax=float(np.max(np.abs(per)))
        sres,lab=subgroup_reslb(per,m,M) if full else (None,None)
        floor=math.sqrt(n*math.log(p/n))
        sr=f"{sres:.3f}" if sres is not None else "  n/a"
        srf=f"{sres/floor:.4f}" if sres is not None else "  n/a"
        srt=f"{sres/truemax:.4f}" if sres is not None else "  n/a"
        print(f"{n:>5} {p:>11} {m:>9} {str(full):>5} {truemax:>9.3f} {sr:>9} {floor:>9.3f} {truemax/floor:>9.4f} {srf:>11} {srt:>11}")
        rows.append((n,truemax/floor, sres/floor if sres is not None else None))
    print("\nHONEST GROWTH (FIXED beta): true/floor vs log2(n):")
    full_rows=[(n,tf,sf) for n,tf,sf in rows]
    xs=[math.log2(n) for n,_,_ in full_rows]; ys=[tf for _,tf,_ in full_rows]
    if len(xs)>=3:
        nn=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
        slope=(nn*sxy-sx*sy)/(nn*sxx-sx*sx)
        print(f"  slope d(true/floor)/d(log2 n) = {slope:+.4f}")
    sfr=[(n,sf) for n,_,sf in full_rows if sf is not None]
    if len(sfr)>=3:
        xs2=[math.log2(n) for n,_ in sfr]; ys2=[sf for _,sf in sfr]
        nn=len(xs2); sx=sum(xs2); sy=sum(ys2); sxx=sum(x*x for x in xs2); sxy=sum(x*y for x,y in zip(xs2,ys2))
        slope2=(nn*sxy-sx*sy)/(nn*sxx-sx*sx)
        print(f"  slope d(subResLB/floor)/d(log2 n) = {slope2:+.4f}")
        verdict = "GROWS (Omega disproof)" if slope2>0.05 else "FLAT/DECAYS -> resonator does NOT concentrate; no Omega growth (floor tight)"
        print(f"  RESONATOR VERDICT: {verdict}")
