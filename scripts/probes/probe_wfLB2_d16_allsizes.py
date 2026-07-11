#!/usr/bin/env python3
"""LB2 adversarial: mirror the d=32 route-i break mechanism EXACTLY at d=16.
The d=32 break used antipodal-free configs of size 12 (NOT half-sets) with p_1=0 mod p.
So at d=16 we must check ALL antipodal-free subset sizes (not just |Y|=8) for a
char-p p_1=0 primitive point, and the higher-odd-power profile, over a WIDE prime band
(test p-independence past 2^12, per the live-intel decisive test)."""
import itertools
from math import gcd
from functools import reduce

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primes_1_mod_n(nn, lo, cap):
    out=[]; p=lo|1
    while len(out)<cap:
        if (p-1)%nn==0 and is_prime(p): out.append(p)
        p+=2
    return out
def find_gen(p, nn):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//nn,p)
        if pow(w,nn,p)==1 and all(pow(w,nn//q,p)!=1 for q in (2,3,5,7) if nn%q==0):
            return w
    raise RuntimeError("nogen")

n=16; half=8
# char-0: enumerate ALL antipodal-free subsets (any size>=2), coordinate vector over Z[zeta16].
def coordvec(Y):
    v=[0]*half
    for j in Y:
        e=j%n
        if e<half: v[e]+=1
        else: v[e-half]-=1
    return tuple(v)

print("="*86)
print("LB2 adversarial: ALL antipodal-free subset sizes at d=16 (mirror the d=32 break)")
print("="*86)
# char-0 gcd: the product of gcds over ALL antipodal-free subsets = the full R_16^(p1,all-sizes)
worst_gcd=1; cnt=0; zero_over_C=0; gcds=set()
for size in range(2, half+1):       # antipodal-free => max size = half = 8
    for Y in itertools.combinations(range(n), size):
        Ys=set(Y)
        if any(((j+half)%n) in Ys for j in Y): continue
        v=coordvec(Y); cnt+=1
        if all(x==0 for x in v): zero_over_C+=1
        g=reduce(gcd,[abs(x) for x in v],0)
        gcds.add(g)
        if g>worst_gcd: worst_gcd=g
print(f"char-0: ALL antipodal-free subsets (size 2..8): {cnt}")
print(f"  with p_1=0 over C (Lam-Leung says 0): {zero_over_C}")
print(f"  distinct coordinate-vector gcds: {sorted(gcds)}   worst gcd: {worst_gcd}")
print(f"  => R_16^(p1, all sizes) prime factors come ONLY from gcds {sorted(gcds-{1}) or 'NONE (all gcd 1)'}")

# char-p WIDE band: any antipodal-free subset (any size) with p_1=0 mod p that is char-0-nonzero
print("\nchar-p WIDE band (test p-independence past 2^12):")
bands=[(16**2,'~16^2'),(16**3,'~16^3'),(16**4,'~16^4'),(16**5,'~16^5'),(2**20,'~2^20')]
for lo,lbl in bands:
    ps=primes_1_mod_n(16, lo, cap=6)
    found_any=False
    for p in ps:
        w=find_gen(p,16); R=[pow(w,j,p) for j in range(16)]
        hit=None
        for size in range(2,half+1):
            for Y in itertools.combinations(range(n),size):
                Ys=set(Y)
                if any(((j+half)%n) in Ys for j in Y): continue
                if sum(R[j] for j in Y)%p==0:
                    # char-0 nonzero?
                    v=coordvec(Y)
                    if any(x!=0 for x in v):
                        hit=(Y,size); break
            if hit: break
        if hit: found_any=True
    print(f"  band {lbl} ({len(ps)} primes up to {ps[-1]}): "
          f"{'SPURIOUS p_1=0 found '+str(hit) if found_any else 'NONE (Q1 p1-face holds)'}")
print("\nVERDICT: if all gcds=1 and no char-p spurious across all bands => d=16 p1-face Q1 holds")
print("         char-uniformly (the gcd-1 fact is prime-INDEPENDENT, exactly the live-intel test).")
