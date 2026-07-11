#!/usr/bin/env python3
"""
#407 STRATEGY 2 — pin the threshold for A_r <= Wick, and decompose the ANOMALY exactly.

KEY FACTS to establish:
 (F1) A_r(F_p) = E_r^{(0)}(ring)  +  Anomaly_r(p)  -  n^{2r}/p,
      where E_r^{(0)}(ring) = #{(x,y) in mu_n^{2r} : sum x = sum y in Z[zeta_n]} (char-0 count),
      Anomaly_r(p) = #{(x,y) : sum x = sum y mod p in F_p, but NOT in Z[zeta_n]}.
 (F2) char-0:  E_r^{(0)}(ring) <= Wick = (2r-1)!! n^r  (PROVEN, Lam-Leung; DyadicEnergyK1).
      Actually E_r^{(0)}(ring) - n^{2r}/p < Wick always? The DC term n^{2r}/p is the b=0 share.
      We have E_r(F_p) = (1/p) sum_b |eta_b|^{2r} INCLUDING b=0 = n^{2r}.
      So A_r = E_r(F_p) - n^{2r}/p.   And E_r(F_p)*p = #{(x,y): sum=sum mod p} (4r-tuple count).
 (F3) THE TARGET A_r <= Wick  <=>  E_r(F_p) <= Wick + n^{2r}/p
      <=> p*E_r(F_p) <= p*Wick + n^{2r}.
      The char-0 ring count R_r := #{(x,y) in mu_n^{2r}: sum x = sum y in ring}.
      p*E_r(F_p) = R_r + AnomCount_r  where AnomCount_r = char-p-only collisions.
      Target  <=>  R_r + AnomCount_r <= p*Wick + n^{2r}.
      Since R_r <= p*Wick? NO: R_r is a fixed integer ~ Wick*n^r... let's measure R_r vs the pieces.

We compute R_r (ring count) EXACTLY using the integer coordinate vectors of mu_n in Z[zeta_n]
(basis {zeta^j : 0<=j<n/2}, zeta^{n/2} = -1), and the F_p count by convolution, to separate
the anomaly cleanly.
"""
import math
from sympy import primerange, primitive_root
import numpy as np
from itertools import product

def coord_vectors(n):
    """mu_n elements as integer vectors in Z^{n/2} (basis zeta^0..zeta^{n/2-1}, zeta^{n/2}=-1)."""
    h = n//2
    V = []
    for j in range(n):
        v = [0]*h
        if j < h:
            v[j] = 1
        else:
            v[j-h] = -1
        V.append(tuple(v))
    return V

def ring_energy_count(n, r):
    """R_r = #{(x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x = sum y in Z[zeta_n]}.
    Equivalent: #{ r-tuples summing to v } squared, summed over v (as integer vectors)."""
    V = coord_vectors(n)
    # count r-fold sums
    from collections import defaultdict
    cnt = defaultdict(int)
    # build distribution of sum of r vectors
    # start with single
    dist = defaultdict(int)
    dist[tuple([0]*(n//2))] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for v in V:
                key = tuple(a+b for a,b in zip(s,v))
                nd[key] += c
        dist = nd
    R = sum(c*c for c in dist.values())
    return R

def fp_energy_count(n, r, p):
    """p * E_r(F_p) = #{(x,y) in mu_n^{2r} : sum x = sum y mod p}.
    Compute as sum over residues of (count of r-tuples summing to that residue)^2."""
    g = int(primitive_root(p))
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            break
    mu = [pow(z, j, p) for j in range(n)]
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=np.int64)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return int((cnt.astype(np.float64)**2).sum())

def doublefact(r):
    d=1.0
    for j in range(1,2*r,2): d*=j
    return d

def main():
    print("="*120)
    print("Decompose: p*E_r(F_p) vs Ring count R_r vs p*Wick + n^{2r}.  TARGET: p*E_r <= p*Wick + n^{2r}")
    print("Anomaly AnomCount = p*E_r(F_p) - R_r  (char-p-only collisions, >= 0).")
    print("="*120)
    for n in [8, 16, 32]:
        print(f"\n##### mu_{n} #####")
        rmax = 5 if n<=16 else 4
        # ring counts (p-independent)
        Rr = {r: ring_energy_count(n, r) for r in range(1, rmax+1)}
        Wick = {r: doublefact(r)*n**r for r in range(1, rmax+1)}
        print("  Ring R_r:", {r: Rr[r] for r in range(1,rmax+1)})
        print("  Wick   :", {r: Wick[r] for r in range(1,rmax+1)})
        print("  R_r/Wick:", {r: round(Rr[r]/Wick[r],3) for r in range(1,rmax+1)})
        # primes spanning beta 1.3 .. 4
        for beta in [1.5, 2.0, 2.5, 3.0, 4.0]:
            target = int(n**beta)
            p = next((q for q in primerange(target, target*3) if q % n == 1), None)
            if p is None: continue
            print(f"  --- p={p} (beta={math.log(p)/math.log(n):.2f}) ---")
            for r in range(1, rmax+1):
                pEr = fp_energy_count(n, r, p)
                anom = pEr - Rr[r]
                Ar = pEr/p - (n**(2*r))/p
                rhs = p*Wick[r] + n**(2*r)
                ok = "OK " if pEr <= rhs else "BAD"
                print(f"      r={r}: p*E_r={pEr:14d}  R_r={Rr[r]:12d}  Anom={anom:12d}  "
                      f"A_r/Wick={Ar/Wick[r]:.3f}  [{ok}] (Anom vs n^{{2r}}/p shift: n^2r={n**(2*r)})")

if __name__ == "__main__":
    main()
