#!/usr/bin/env python3
"""
#407 C2 SCAN — moment anomaly #spurious_r per (mu,r), printed INCREMENTALLY,
to pin the crossover r* across mu=6..10 and confirm r* ~ beta (=4) for p~n^4.

Method (exact, cheap): r-fold sum distribution by RING coordinate (small support);
#spurious_r = (F_p collisions) - (ring collisions), computed by bucketing the ring
classes by their F_p image. Prints each r as soon as it is done, with a hard wall-time
guard per (mu,r) via support cap.
"""
import sys, math, time
from collections import defaultdict
from sympy import isprime, primitive_root

def prize_prime(mu, beta_target=4):
    n = 2**mu
    target = n**beta_target
    p = target - (target % n) + 1
    if p <= target: p += n
    while not isprime(p):
        p += n
    return n, p

def dfo(r):
    v=1
    for k in range(1,2*r,2): v*=k
    return v

def fp_root(n,p):
    return pow(primitive_root(p),(p-1)//n,p)

def scan(mu, rmax, support_cap):
    n,p = prize_prime(mu)
    beta = math.log(p)/math.log(n)
    h=n//2
    g=fp_root(n,p)
    gpow=[pow(g,j,p) for j in range(h)]
    root_vecs=[]
    for j in range(n):
        v=[0]*h
        if j<h: v[j]+=1
        else: v[j-h]-=1
        root_vecs.append(tuple(v))
    print(f"=== mu={mu} n={n} p={p} beta={beta:.3f} (beta+1={beta+1:.2f}) support_cap={support_cap} ===", flush=True)
    print(f"  {'r':>2} {'#spurious':>14} {'E_r(F_p)':>16} {'E_ring':>16} {'Wick':>16} "
          f"{'n^2r/p':>14} {'ratio':>11} {'sec':>6}", flush=True)
    cur=defaultdict(int)
    for v in root_vecs: cur[v]+=1
    r=1
    while r<rmax:
        r+=1
        t0=time.time()
        # convolve to dist_r
        nxt=defaultdict(int)
        for v,c in cur.items():
            for rv in root_vecs:
                nxt[tuple(a+b for a,b in zip(v,rv))]+=c
        cur=nxt
        if len(cur)>support_cap:
            print(f"  {r:>2}  support {len(cur)} > cap, stop", flush=True)
            break
        E_ring=sum(c*c for c in cur.values())
        fp_bucket=defaultdict(int)
        for coord,c in cur.items():
            img=0
            for j,cj in enumerate(coord):
                if cj: img=(img+cj*gpow[j])%p
            fp_bucket[img]+=c
        E_fp=sum(c*c for c in fp_bucket.values())
        spur=E_fp-E_ring
        wick=dfo(r)*(n**r)
        triv=(n**(2*r))/p
        ratio=spur/triv if triv>0 else float('inf')
        print(f"  {r:>2} {spur:>14} {E_fp:>16} {E_ring:>16} {wick:>16} "
              f"{triv:>14.2f} {ratio:>11.5f} {time.time()-t0:>6.1f}", flush=True)
    print(flush=True)

if __name__=="__main__":
    # mu: (rmax, support_cap)
    plan = {6:(6,6_000_000), 7:(5,6_000_000), 8:(5,6_000_000), 9:(4,6_000_000), 10:(4,6_000_000)}
    only = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv)>1 else list(plan.keys())
    for mu in only:
        rmax,cap = plan.get(mu,(4,6_000_000))
        scan(mu,rmax,cap)
