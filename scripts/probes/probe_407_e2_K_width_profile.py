#!/usr/bin/env python3
"""
probe_407_e2_K_width_profile.py  (#444 — K(n,w) width profile: where does n*K cross budget?)

Found: the e2=0 census at the EXTREMAL width w=n/2 has #bad=n*K with K=1,3,38 (n=8,16,32), i.e.
n*K ~ n^3.6 — SUPER-Johnson (Johnson #bad-scale ~ n*sqrt(n)=n^1.5). So w=n/2 is NOT the binding width;
the binding (= delta*) is the SMALLEST agreement deficit, i.e. the width w where the e2=0 (or general
over-det) bad-count first drops to <= budget=n. The actual delta* = 1 - s*/n with s* = n - w* and w* the
binding width.

But the e2=0 locus is specifically the s-k=2 (depth-2 over-det) family at agreement size s where the
DEFICIT is e2-type. The honest object: profile the e2=0 bad-count #bad(n,w) as w ranges, find w* where
n*K(n,w) (or raw #bad) crosses budget n, and read delta*. Compare to Johnson + floor. AND apply the
rule-3 thinness gate at the BINDING width (not just w=n/2): is the crossing width w* thinness-essential?

NOTE on object: the e2=0 condition is the depth-2 over-determination for a SPECIFIC pencil. Here I profile
the e2=0 census across widths w (size of S) as the cleanest proxy for the over-det deficit curve, exact.

METHOD: exact e2=0 enumeration via antipodal-pair meet-in-middle (validated vs in-tree K=1,3,38), for all
widths w from small up to n/2, n in {8,16,32}. Report #bad(w), K(w), and the budget-crossing width w*.
Prize prime, proper subgroup, never n=q-1. Python-only => axiom-clean trivially.
"""
import math, time
import numpy as np

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

def e2_census_allwidths(n,p):
    """exact #bad-alpha + K for EVERY width w (2..n), via antipodal-pair MIM. returns dict w->(dist,K)."""
    g=proot(p); m=(p-1)//n; h=pow(g,m,p)
    mu=[pow(h,i,p) for i in range(n)]
    half=n//2
    pairs=[]
    for i in range(half):
        lo=mu[i]; hi=mu[i+half]
        pairs.append([(0,0,0),(1,lo%p,(lo*lo)%p),(1,hi%p,(hi*hi)%p),(2,0,(2*lo*lo)%p)])
    A=pairs[:half//2]; B=pairs[half//2:]
    def enum(side):
        res={}
        def rec(idx,cnt,e1,p2):
            if idx==len(side):
                res.setdefault(cnt,[]).append((e1%p,p2%p)); return
            for (dc,de1,dp2) in side[idx]:
                rec(idx+1,cnt+dc,e1+de1,p2+dp2)
        rec(0,0,0,0); return res
    Ares=enum(A); Bres=enum(B)
    # precompute B arrays per count
    Barr={c:np.array(v,dtype=np.int64) for c,v in Bres.items()}
    out={}
    for w in range(2,n+1):
        alphas=set()
        for cA,lstA in Ares.items():
            cB=w-cA
            if cB not in Barr: continue
            Bv=Barr[cB]; e1B=Bv[:,0]; p2B=Bv[:,1]; tB=(e1B*e1B-p2B)%p
            for (e1A,p2A) in lstA:
                tA=(e1A*e1A-p2A)%p
                tot=(tA+tB+(2*e1A%p)*e1B)%p
                e1tot=(e1A+e1B)%p
                mask=(tot==0)&(e1tot!=0)
                for v in e1tot[mask].tolist(): alphas.add((-pow(int(v),p-2,p))%p)
        if alphas:
            rem=set(alphas); K=0
            while rem:
                x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
            out[w]=(len(alphas),K)
        else:
            out[w]=(0,0)
    return out

def main():
    print("="*78); print("e2=0 census WIDTH PROFILE — where does #bad cross budget=n? (delta* read-off)"); print("="*78)
    for n in (8,16,32):
        p=prize_prime(n,4); t0=time.time()
        prof=e2_census_allwidths(n,p)
        budget=n
        # delta* = 1 - s*/n, s* = max agreement size with #bad<=budget. agreement size s = ... here width w
        # is the SUBSET size; the e2=0 family lives at a fixed deficit. We read: which w have #bad<=budget.
        good_w=[w for w,(d,K) in prof.items() if d<=budget]
        sJ=math.sqrt(n)  # johnson-ish agreement scale
        print(f"\n--- n={n} p={p} budget={budget} [{time.time()-t0:.1f}s] ---")
        print(f"    w : #bad(distinct-alpha)  K")
        for w in sorted(prof):
            d,K=prof[w]
            mark=" <=budget" if d<=budget else " >budget"
            if d>0 or w<=n//2+1:
                print(f"    {w:3d}: {d:8d}  K={K:5d}{mark}")
        # the binding: largest w with #bad<=budget that is NOT trivially small (the floor of the over-det)
        print(f"    widths with #bad<=budget: {good_w}")

if __name__=="__main__":
    main()
