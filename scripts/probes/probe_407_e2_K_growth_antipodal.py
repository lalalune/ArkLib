#!/usr/bin/env python3
"""
probe_407_e2_K_growth_antipodal.py  (#444 — the K(n) growth law, antipodal-structured enumeration)

I established: the e2=0 over-det census (the prize FLOOR's R1 object, #bad=n*K) is thin-ONLY, and EVERY
e2=0 subset contains >=1 antipodal pair (x, -x = h^{n/2}x). K=1,3,38 at n=8,16,32. The K growth law is the
isolated open prize content. Goal: a 4th data point / structural law, using the antipodal mechanism to
beat the C(n,n/2) wall.

KEY STRUCTURE: index mu_n so antipode(i) = i + n/2 (mod n). For S a w=n/2 subset write it by how it meets
each antipodal PAIR {i, i+n/2}, i in [0,n/2): each pair is BOTH-in / LOW-only / HIGH-only / NEITHER.
e1(S) = sum of chosen; e2 via power sums. Antipodal pair {x,-x} contributes x+(-x)=0 to e1 and
x^2+x^2=2x^2 to p2. So pairs are "e1-neutral, p2-active". This lets us enumerate over the (4^{n/2}) pair-
patterns with the |S|=n/2 constraint — still large, BUT we can use MEET-IN-MIDDLE over the n/2 pairs
splitting into two halves of n/4 pairs each, matching on (e1, p2) the same way probe_e2_n32 did but on the
PAIR structure (fewer effective dof). We just RE-VERIFY K at n=8,16,32 with this method (cross-check the
in-tree 1,3,38) and characterize the growth, and ATTEMPT n=64 if the pair-MIM is feasible.

We also extract the STRUCTURAL law: fit K(n) and #bad=n*K vs candidate laws (Johnson n^{1/2}-ish? n/log n
floor? quadratic? the additive-energy E_2 ~ n^{?}). The verdict feeds the floor-vs-Johnson question
DIRECTLY: if n*K(n) ~ n*sqrt(n) the census tracks Johnson; if n*K grows faster the census is super-Johnson.

Exact mod-p, prize prime, proper subgroup, never n=q-1. Python-only => axiom-clean trivially.
"""
import itertools, math
from itertools import combinations
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

def K_via_pairs(n,p):
    """exact #bad-alpha and K, enumerating w=n/2 subsets via antipodal-pair patterns + meet-in-middle.
       antipode(i)=i+n/2. half-pairs: P = n/2 pairs. Each pair state s in {0:neither,1:low i,2:high i+n/2,
       3:both}. |S| = sum over pairs of popcount(state in {1,2}=1, 3=2). Need total = w=n/2.
       e1 = sum chosen; e2=0 <=> e1^2==p2. Split P pairs into A (first P//2) and B (rest), match on
       (e1, p2, count) so that countA+countB=w and (e1A+e1B)^2==p2A+p2B, e1!=0."""
    g=proot(p); m=(p-1)//n; h=pow(g,m,p)
    mu=[pow(h,i,p) for i in range(n)]
    half=n//2
    w=half
    # value of index i is mu[i]; antipode index i+half has value mu[i+half] = -mu[i] (since h^half=-1)
    # per pair i in [0,half): choices contribute (delta_count, e1_contrib, p2_contrib)
    # state0 neither: (0,0,0); state1 low(i): (1, mu[i], mu[i]^2); state2 high(i+half): (1, mu[i+half], mu[i+half]^2);
    # state3 both: (2, mu[i]+mu[i+half]=0, mu[i]^2+mu[i+half]^2=2 mu[i]^2)
    pairs=[]
    for i in range(half):
        lo=mu[i]; hi=mu[i+half]
        states=[(0,0,0),(1,lo%p,(lo*lo)%p),(1,hi%p,(hi*hi)%p),(2,0,(2*lo*lo)%p)]
        pairs.append(states)
    A=pairs[:half//2]; B=pairs[half//2:]
    def enum(side):
        # dict keyed by (count) -> list of (e1,p2)
        res={}
        def rec(idx,cnt,e1,p2):
            if idx==len(side):
                res.setdefault(cnt,[]).append((e1%p,p2%p)); return
            for (dc,de1,dp2) in side[idx]:
                if cnt+dc<=w:
                    rec(idx+1,cnt+dc,e1+de1,p2+dp2)
        rec(0,0,0,0)
        return res
    Ares=enum(A); Bres=enum(B)
    alphas=set(); nbad=0
    for cA,lstA in Ares.items():
        cB=w-cA
        if cB not in Bres: continue
        lstB=Bres[cB]
        # for each (e1A,p2A) need (e1B,p2B) with (e1A+e1B)^2 == p2A+p2B, e1A+e1B != 0
        # build hash of B by key = (p2B - e1B^2)? we need (e1A+e1B)^2 - (p2A+p2B)=0
        #   = e1A^2 + 2 e1A e1B + e1B^2 - p2A - p2B = 0
        #   = (e1A^2 - p2A) + (e1B^2 - p2B) + 2 e1A e1B = 0
        # depends on product e1A*e1B -> can't pure-hash. But |lstA|,|lstB| are small here. nested loop.
        Barr=np.array(lstB,dtype=np.int64)
        e1B=Barr[:,0]; p2B=Barr[:,1]
        tB=(e1B*e1B - p2B)%p
        for (e1A,p2A) in lstA:
            tA=(e1A*e1A - p2A)%p
            tot=(tA + tB + (2*e1A%p)*e1B)%p
            e1tot=(e1A + e1B)%p
            mask=(tot==0)&(e1tot!=0)
            good=e1tot[mask]
            nbad+=int(good.size)
            for v in good.tolist(): alphas.add((-pow(int(v),p-2,p))%p)
    # K = orbit count under mu
    rem=set(alphas); K=0
    while rem:
        x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
    return nbad, len(alphas), K

def main():
    print("="*78); print("e2=0 census K(n) growth law via antipodal-pair meet-in-middle (cross-check + extend)"); print("="*78)
    data=[]
    for n in (8,16,32,64):
        try:
            p=prize_prime(n,4)
            import time; t0=time.time()
            nbad,dist,K=K_via_pairs(n,p)
            dt=time.time()-t0
            data.append((n,K,dist))
            print(f"  n={n:3d} p={p} w={n//2}:  #bad-alpha(distinct)={dist}  K(orbits)={K}  n*K={n*K}  [{dt:.1f}s]  (in-tree K: 1,3,38 @ 8,16,32)")
        except Exception as e:
            print(f"  n={n}: FAILED/infeasible: {e}")
            break
    # growth-law fit
    if len(data)>=3:
        print("\n  GROWTH LAW fit (K vs n):")
        ns=[d[0] for d in data]; Ks=[d[1] for d in data]
        for i in range(1,len(data)):
            r=Ks[i]/Ks[i-1] if Ks[i-1] else float('inf')
            slope=math.log(Ks[i]/Ks[i-1])/math.log(ns[i]/ns[i-1]) if Ks[i-1]>0 and Ks[i]>0 else float('nan')
            print(f"    n {ns[i-1]}->{ns[i]}: K {Ks[i-1]}->{Ks[i]}  ratio={r:.2f}  loglog-slope={slope:.3f}")
        # compare n*K to Johnson n*sqrt(n) and floor n*(n/log n)
        print("\n  n*K vs Johnson-scale (n*sqrt n) vs energy-scale:")
        for (n,K,dist) in data:
            nK=n*K; johnson=n*math.sqrt(n); print(f"    n={n}: n*K={nK}  n^1.5={johnson:.0f}  nK/n^1.5={nK/johnson:.3f}  nK/n^2={nK/n**2:.3f}  nK/n^2.5={nK/n**2.5:.4f}")

if __name__=="__main__":
    main()
