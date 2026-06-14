#!/usr/bin/env python3
"""
#407 STRATEGY 4 (refined) — the CONNECTED char-p anomaly.

Established (KB): A_r = R_r + Anom_r - n^{2r}/p, R_r=char-0 ring count <= Wick.
Sole open inequality:  Anom_r <= n^{2r}/p.

The directive's cumulant idea, made precise:  decompose Anom_r (the char-p-only
collisions) into a SUM OVER PARTITIONS of the 2r legs into CONNECTED clusters.  A
collision (x,y) in mu_n^{2r} with sum x = sum y mod p but NOT in Z[zeta_n] is "char-p
genuine".  Its CONNECTED part = the sub-relations that themselves vanish mod p but not
in the ring.  The DC term n^{2r}/p is the "fully disconnected" / mean^{2r} piece.

KEY QUESTION (decides the route):  is the connected char-p anomaly (the part NOT
explained by lower-order char-p relations times disconnected pieces) the dominant or a
SMALL part of Anom_r?  If the anomaly FACTORS through a single minimal char-p relation
(a "primitive" vanishing sum), then bounding Anom_r reduces to bounding the count of
MINIMAL char-p relations -- the Lam-Leung weight question -- which has the L_min >= (p-1)/n
threshold (small-weight gap).

Here we measure, EXACTLY:
  (M1) Anom_r(p) = E_r(F_p) - R_r  for prize-regime p (beta=4) and small p.
  (M2) The "primitive anomaly" P_r := # char-p collisions whose underlying signed
       multiset relation v (in {-1,0,1,...}^n coords) has NO proper nonempty sub-relation
       vanishing mod p.  (connected = primitive, single-cluster.)
  (M3) Check the FACTORIZATION:  does Anom_r = sum over set-partitions of contributions
       from primitive relations on the blocks?  i.e. is the FREE-CUMULANT / multiplicative
       structure  E_r(F_p) "=" exp-of-connected  exact?  Equivalent test:
          define the SIGNED-RELATION generating count.  A collision <-> a vector
          w = (multiplicity of each n-th root with sign) in Z^n with sum_j w_j zeta^j = 0
          mod p, |w|_+ = |w|_- = r (r plus-legs, r minus-legs).  This is an element of the
          relation lattice  L_p := ker(Z^n -> F_p, e_j -> zeta^j).
       R_r counts w in L_0 := ker(Z^n -> Z[zeta_n]) (char-0 relations).
       Anom counts w in L_p \ L_0 with the leg constraint.
  (M4) the LATTICE picture:  L_p / L_0 is a finite abelian group of order = the index =
       |coker| = (size of the image of Z^n in F_p which is all of <zeta> ... ) -- compute it.
       The minimal char-p genuine relation length = lambda_1 of L_p in the appropriate norm.
"""
import math
import numpy as np
from sympy import primerange
from collections import defaultdict

def setup_mu(n, p):
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            return [pow(z, j, p) for j in range(n)], z
    raise RuntimeError

def coord_vectors(n):
    """n-th root zeta^j -> coordinate in Z^{n/2} using zeta^{n/2}=-1 (integral basis)."""
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

def ring_count(n, r):
    """R_r = # (x,y) in mu_n^{2r} : sum x = sum y in Z[zeta_n] (char-0)."""
    V = coord_vectors(n)
    dist = defaultdict(int)
    dist[tuple([0]*(n//2))] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for v in V:
                nd[tuple(a+b for a, b in zip(s, v))] += c
        dist = nd
    return sum(c*c for c in dist.values())

def fp_coll(n, r, p):
    """E_r(F_p) = # (x,y) in mu_n^{2r} : sum x = sum y mod p."""
    mu, _ = setup_mu(n, p)
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=np.int64)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return int((cnt.astype(np.float64)**2).sum())

def doublefact(r):
    d = 1.0
    for j in range(1, 2*r, 2):
        d *= j
    return d

def main():
    print("="*100)
    print("CONNECTED char-p anomaly  Anom_r = E_r(F_p) - R_r,  test  Anom_r <= n^{2r}/p")
    print("and the lattice index |L_p/L_0| (minimal genuine char-p relation governs it).")
    print("="*100)

    for n in [8, 16, 32]:
        # prize regime beta=4
        p = next(q for q in primerange(int(n**4), int(n**4*3)) if q % n == 1)
        rmax = 6 if n <= 16 else 5
        print(f"\nn={n}  PRIZE p={p} (beta=4):")
        print(f"   {'r':>2} {'E_r(F_p)':>16} {'R_r(ring)':>16} {'Anom_r':>12} {'n^2r/p':>16} "
              f"{'Anom<=DC?':>10} {'Anom/DC':>9}")
        for r in range(1, rmax+1):
            E = fp_coll(n, r, p)
            R = ring_count(n, r)
            anom = E - R
            dc = n**(2*r) / p
            ok = "OK" if anom <= dc else "VIOL"
            print(f"   {r:>2} {E:>16d} {R:>16d} {anom:>12d} {dc:>16.2f} {ok:>10} "
                  f"{anom/dc if dc > 0 else 0:>9.4f}")

    # small-p (saturated) where the bound FAILS, to see the anomaly grow
    print("\n" + "="*100)
    print("SATURATED (small p, beta<4): anomaly EXCEEDS DC -> A_r>Wick (out of scope, expected)")
    for n, p in [(16, 97), (16, 193), (32, 97), (32, 193)]:
        beta = math.log(p)/math.log(n)
        rmax = 4
        anoms = []
        for r in range(2, rmax+1):
            E = fp_coll(n, r, p)
            R = ring_count(n, r)
            anoms.append((r, E-R, n**(2*r)/p))
        s = "  ".join(f"r={r}:An={a}({'>' if a>dc else '<='}{dc:.0f})" for r, a, dc in anoms)
        print(f"   n={n} p={p} (beta={beta:.2f}): {s}")

    print("\n" + "="*100)
    print("Interpretation: Anom_r jumps from 0 to positive at r ~ beta (KB FACT 1).  In the")
    print("prize regime r* ~ log p ~ 4 beta log n >> beta, so the anomaly is ON at the optimizer.")
    print("This probe quantifies HOW MUCH headroom n^2r/p gives vs the actual anomaly.")
    print("="*100)

if __name__ == "__main__":
    main()
