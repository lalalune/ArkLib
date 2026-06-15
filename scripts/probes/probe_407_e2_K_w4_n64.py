#!/usr/bin/env python3
"""
probe_407_e2_K_w4_n64.py  (#444 — the shallow-width K(n,w=4) growth law to n=64, 4-point fit)

The e2=0 census width profile isolated the cleanest sub-sequence at the SHALLOWEST over-det width
w=k+2=4: K = 1,3,7 (#bad = 8,48,224) at n=8,16,32. At w=4 the locus is just 4-subsets, directly
enumerable (C(n,4) ~ n^4/24; n=64 => ~635k), NO meet-in-middle needed. Push to n=64 (and n=48) for a
4-point growth-law fit on K(n,4) and #bad(n,4)=n*K, to sharpen the Johnson-vs-floor read:
  - Johnson #bad-scale ~ n*sqrt(n) = n^1.5 ; floor needs #bad ~ budget = n (K=O(1)).
  - observed (3pt) #bad(w=4) ~ n^2.4, super-budget and growing. A 4th point pins the exponent.

Exact, proper subgroup mu_n, prize prime p~n^4, never n=q-1. Python-only => axiom-clean trivially.
"""
import math, time
from itertools import combinations

def is_prime(x):
    if x<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x%q==0: return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y=pow(a,d,x)
        if y==1 or y==x-1: continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True;break
        if not ok: return False
    return True
def factor(x):
    f=[];d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:f.append(x)
    return f
def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 0
def prize_prime(n,beta=4):
    p=n**beta; p-=p%n; p+=1
    while True:
        if p%n==1 and is_prime(p): return p
        p+=n

def K_w4(n,p):
    """exact #bad-alpha and K over 4-subsets S with e2(S)=0, e1(S)!=0. alpha=-1/e1. K=#mu-orbits."""
    g=proot(p); m=(p-1)//n; h=pow(g,m,p)
    mu=[pow(h,i,p) for i in range(n)]
    mu2=[(v*v)%p for v in mu]
    alphas=set(); nbad=0
    # iterate 4-subsets; incremental e1,p2
    for S in combinations(range(n),4):
        e1=(mu[S[0]]+mu[S[1]]+mu[S[2]]+mu[S[3]])%p
        p2=(mu2[S[0]]+mu2[S[1]]+mu2[S[2]]+mu2[S[3]])%p
        if (e1*e1-p2)%p==0 and e1!=0:
            nbad+=1; alphas.add((-pow(e1,p-2,p))%p)
    rem=set(alphas); K=0
    while rem:
        x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
    return nbad, len(alphas), K

def main():
    print("="*78); print("e2=0 census at SHALLOW width w=4: K(n,4) growth to n=64 (4-point fit)"); print("="*78)
    data=[]
    for n in (8,16,32,48,64):
        p=prize_prime(n,4); t0=time.time()
        nbad,dist,K=K_w4(n,p)
        dt=time.time()-t0
        data.append((n,dist,K))
        print(f"  n={n:3d} p={p:>12d}: #bad-sets={nbad:6d}  #distinct-alpha={dist:5d}  K={K:4d}  n*K={n*K:6d}  [{dt:.1f}s]")
    print("\n  GROWTH-LAW FIT on #distinct-alpha (=#bad) at w=4:")
    import numpy as np
    ns=np.array([d[0] for d in data]); nb=np.array([max(d[1],1) for d in data]); Ks=np.array([max(d[2],1) for d in data])
    A=np.vstack([np.log(ns),np.ones(len(ns))]).T
    sl,ic=np.linalg.lstsq(A,np.log(nb),rcond=None)[0]
    slK,icK=np.linalg.lstsq(A,np.log(Ks),rcond=None)[0]
    print(f"    #bad(w=4) ~ {math.exp(ic):.4f} * n^{sl:.3f}   |   K(w=4) ~ {math.exp(icK):.4f} * n^{slK:.3f}")
    for i in range(1,len(data)):
        n0,d0,k0=data[i-1]; n1,d1,k1=data[i]
        s=math.log(max(d1,1)/max(d0,1))/math.log(n1/n0)
        print(f"    n {n0}->{n1}: #bad {d0}->{d1}  K {k0}->{k1}  #bad-loglog-slope={s:.3f}")
    print(f"\n  Johnson #bad-scale = n^1.5 ; budget = n^1.0 (floor needs K=O(1)).")
    print(f"  => #bad(w=4) exponent {sl:.2f} is {'ABOVE Johnson (super-Johnson census)' if sl>1.5 else 'at/below Johnson'};"
          f" {'>budget, grows (NOT floor)' if sl>1.0 else 'budget-bounded'}.")

if __name__=="__main__":
    main()
