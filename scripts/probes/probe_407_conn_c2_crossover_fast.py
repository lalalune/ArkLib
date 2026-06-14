#!/usr/bin/env python3
"""
#407 CONNECTION C2 (FAST) — per-r char-p energy anomaly via CONVOLUTION, not n^r enumeration.

E_r = sum over collision classes of (multiplicity)^2, where the multiplicity of a value v is
#{ordered r-tuples of mu_n summing to v}. This is the r-fold AUTOCONVOLUTION of the
1-fold distribution. We compute it incrementally:
   dist_1(v) = 1 for each root v (counted with multiplicity).
   dist_r = dist_{r-1} (*) dist_1   (convolution under the group's addition).

Two ambient groups:
  * F_p:  values live in Z/p (mod-p sums).            -> E_r(F_p)
  * Z[zeta_n]: values live in the coordinate lattice  -> E_r^0 (char-0 ring count).
    Coordinates are length-h=n/2 integer vectors (basis 1,z,...,z^{h-1}, z^h=-1).

#spurious_r = E_r(F_p) - E_r^0  is the char-p EXCESS.

Convolution cost ~ r * (#distinct partial sums) * n  -- feasible to r=6 for n up to ~512
because the number of DISTINCT r-fold sums in F_p is bounded by min(p, n^r) but in the
ring is bounded by the lattice support (polynomially many). We cap the dict size and report.

We also report the Wick value (2r-1)!! n^r for reference, and the trivial floor n^{2r}/p.
"""
import sys, math
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

def double_factorial_odd(r):
    v = 1
    for k in range(1, 2*r, 2):
        v *= k
    return v

def fp_root(n, p):
    g0 = primitive_root(p)
    return pow(g0, (p-1)//n, p)

def energy_fp(mu, p, rmax, dict_cap=40_000_000):
    """E_r(F_p) for r=2..rmax via convolution in Z/p."""
    n = 2**mu
    g = fp_root(n, p)
    roots = [pow(g, j, p) for j in range(n)]
    # dist_1
    dist = defaultdict(int)
    for v in roots:
        dist[v] += 1
    out = {}
    cur = dict(dist)  # dist_1
    for r in range(1, rmax+1):
        if r >= 2:
            # E_r from cur (which is dist_r)
            if len(cur) > dict_cap:
                out[r] = None
            else:
                out[r] = sum(c*c for c in cur.values())
        if r == rmax:
            break
        # convolve cur (*) dist_1  -> dist_{r+1}
        if len(cur) * 1 > dict_cap // n:  # would blow up
            # still try but guard
            pass
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rt in roots:
                nxt[(v + rt) % p] += c
        cur = nxt
        if len(cur) > dict_cap:
            # stop early; remaining r get None
            for rr in range(r+2, rmax+1):
                out[rr] = None
            # but we can still do E_{r+1}
            out[r+1] = sum(c*c for c in cur.values()) if len(cur) <= dict_cap else None
            return out
    return out

def energy_ring(mu, rmax, dict_cap=40_000_000):
    """E_r^0 (char-0) for r=2..rmax via convolution in the Z[zeta_n] coordinate lattice.
    Root j -> coordinate vector: e_j with sign for j>=h. We represent the running sum's
    coordinate vector as a tuple of length h."""
    n = 2**mu
    h = n // 2
    # 1-fold coordinate vectors of the n roots
    root_vecs = []
    for j in range(n):
        vec = [0]*h
        if j < h: vec[j] += 1
        else: vec[j-h] -= 1
        root_vecs.append(tuple(vec))
    dist = defaultdict(int)
    for v in root_vecs:
        dist[v] += 1
    out = {}
    cur = dict(dist)
    for r in range(1, rmax+1):
        if r >= 2:
            out[r] = sum(c*c for c in cur.values()) if len(cur) <= dict_cap else None
        if r == rmax: break
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rv in root_vecs:
                key = tuple(a+b for a,b in zip(v, rv))
                nxt[key] += c
        cur = nxt
        if len(cur) > dict_cap:
            out[r+1] = sum(c*c for c in cur.values()) if len(cur) <= dict_cap else None
            for rr in range(r+2, rmax+1): out[rr] = None
            return out
    return out

def main():
    rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    mus = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [6,7,8]
    print("="*110)
    print(f"CONNECTION C2 FAST — #spurious_r = E_r(F_p) - E_r^0(ring), prize-scale p~n^4, rmax={rmax}")
    print("="*110)
    for mu in mus:
        n, p = prize_prime(mu)
        beta = math.log(p)/math.log(n)
        print(f"\n--- mu={mu} n={n} p={p} beta={beta:.3f} ---")
        efp = energy_fp(mu, p, rmax)
        # ring is p-independent; cap r where lattice support stays small
        erg = energy_ring(mu, rmax)
        print(f"  {'r':>2} {'E_r(F_p)':>16} {'E_r^0(ring)':>16} {'#spurious':>12} "
              f"{'Wick':>18} {'ring/Wick':>9} {'n^2r/p':>14} {'spur/(n2r/p)':>13}")
        for r in range(2, rmax+1):
            Efp = efp.get(r); Erg = erg.get(r)
            wick = double_factorial_odd(r)*(n**r)
            triv = (n**(2*r))/p
            if Efp is None or Erg is None:
                s_fp = str(Efp) if Efp is not None else "(cap)"
                s_rg = str(Erg) if Erg is not None else "(cap)"
                print(f"  {r:>2} {s_fp:>16} {s_rg:>16} {'?':>12} {wick:>18} "
                      f"{(Erg/wick if Erg else 0):>9} {triv:>14.2f}")
                continue
            spur = Efp - Erg
            rw = Erg/wick
            ratio = spur/triv if triv>0 else float('inf')
            print(f"  {r:>2} {Efp:>16} {Erg:>16} {spur:>12} {wick:>18} "
                  f"{rw:>9.4f} {triv:>14.2f} {ratio:>13.6f}")

if __name__ == "__main__":
    main()
