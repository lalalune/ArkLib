"""wf-OT1: d=32 cross-prime survival (the DISCRIMINATING case: 3^16/p ~ 65536/d^4 ~ 0.06 at p~d^4,
but rises near p just above d^4. Confirm cross-prime survival = 0 = noise, per the prior d=32 cleanup)."""
from itertools import product
import random
def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37): 
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True
def primes_1_mod(n,lo,cap):
    out=[];p=lo|1
    while len(out)<cap:
        if (p-1)%n==0 and is_prime(p): out.append(p)
        p+=2
    return out
def root_order(p,d):
    g=2
    while True:
        w=pow(g,(p-1)//d,p)
        if pow(w,d,p)==1 and pow(w,d//2,p)!=1: return w
        g+=1
d=32; half=16
# MITM over 2 halves of 8 pairs each (3^8=6561 each) to make 3^16 feasible
primes=primes_1_mod(d, d**4, 6)
print(f"d={d}, half={half}, 3^{half}={3**half}, primes(p=1 mod {d},>=d^4)={primes}")
def hits_modp(p):
    w=root_order(p,d); b=[pow(w,j,p) for j in range(half)]
    # MITM: c = (cL on j=0..7, cR on j=8..15); sum_L = -sum_R mod p
    from collections import defaultdict
    left=defaultdict(list)
    for cL in product((-1,0,1),repeat=8):
        s=sum(cL[j]*b[j] for j in range(8))%p
        left[s].append(cL)
    res=set()
    for cR in product((-1,0,1),repeat=8):
        s=sum(cR[j]*b[8+j] for j in range(8))%p
        need=(-s)%p
        if need in left:
            for cL in left[need]:
                c=cL+cR
                if any(c): res.add(c)
    return res
sets={}
for p in primes:
    h=hits_modp(p); sets[p]=h
    print(f"  p={p}: per-prime nonempty hits={len(h)} (~3^16/p={3**half/p:.3f})")
common=None
for p in primes:
    common=sets[p] if common is None else (common & sets[p])
print(f"\nCROSS-PRIME survivors over {len(primes)} primes: {len(common)}")
print("   => structural Q1 failure" if common else "   => 0 survivors => mod-p NOISE, Q1(*)_32 CLEAN at prize scale")
