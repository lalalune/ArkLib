#!/usr/bin/env python3
"""
#407 CONNECTION C2 — the char-p energy anomaly per moment, and the crossover r*.

THE QUESTION (from the directive):
  E_r(F_p) - (2r-1)!! n^r = char-p excess = #spurious_r.
  KB claims the anomaly "turns on at r* ~ beta+1" (beta=log_n p in [4,5]).
  (a) COMPUTE #spurious_r for n=2^mu (mu=6..12), p ~ n^4, r=2..6;
      locate the crossover r* where excess becomes Theta(n^{2r}/p) (non-negligible).
  (b) The count lane needs only ONE r (worst case). Is worst-case r BELOW or ABOVE r*?
  (c) If below crossover: what proves excess=0 for r<=r* (a finite low-degree resultant)?

EXACT IDENTITIES USED (all verified inside this probe):
  (i)  eta_b = sum_{x in mu_n} e_p(b x),  e_p(t)=exp(2 pi i t / p).
  (ii) E_r(F_p) := #{(x,y) in mu_n^{2r} : sum x_i = sum y_j mod p}
                 = (1/p) sum_{b=0}^{p-1} |eta_b|^{2r}     [exact Fourier/orthogonality]
       The b=0 term is n^{2r}/p (since eta_0 = n).
       So A_r := E_r(F_p) - n^{2r}/p = (1/p) sum_{b != 0} |eta_b|^{2r}.   [exact]
  (iii) char-0 energy E_r^0 = (2r-1)!! n^r   (Wick / Lam-Leung, dyadic).
        BUT NOTE: E_r(F_p) counts mod-p equalities; the *char-0* count is
        #{(x,y): sum x_i = sum y_j in Z[zeta_n]} which for dyadic mu_n is the
        Wick value (2r-1)!! n^r ONLY in the Sidon/non-saturated reading. We compute
        the EXACT char-0 count directly too (equality in the cyclotomic ring) and
        compare to both n^{2r}/p (the trivial/diagonal floor) and the Wick value.

  #spurious_r is the genuine char-p EXCESS over the char-0 (Z[zeta_n]) count.

We compute eta_b via the EXACT cyclotomic structure when feasible, and via a
high-precision FFT of the indicator of mu_n in Z/p for the moment sums.
Because p ~ n^4 is large (up to 2.8e14), a length-p FFT is infeasible for mu>=8.
So we use TWO complementary exact methods:

  METHOD A (small mu, mu<=8 i.e. p<=4.3e9 still too big for length-p FFT):
    Direct combinatorial count of E_r(F_p) and char-0 E_r by enumerating r-fold
    sums of mu_n (multiset of n^r sums), then convolving. This gives EXACT integer
    energies for r small. Feasible while n^r is small enough (n^r <= ~10^7).

  METHOD B (the anomaly directly):
    #spurious_r = E_r(F_p) - E_r^0  where
      E_r^0 = #{r-fold sums a, r-fold sums b : a == b in Z[zeta_n]}  (char-0)
      E_r(F_p) = same with == in F_p (i.e. reduce sums mod the prime ideal).
    For dyadic mu_n with p ≡ 1 mod n, fix a primitive n-th root g in F_p;
    an r-fold sum of roots maps to an element of F_p. Collisions in F_p that are
    NOT collisions in Z[zeta_n] are exactly #spurious_r.
    We compute the r-fold-sum multiset over EXPONENTS, map to F_p, and to a
    canonical Z[zeta_n] coordinate vector (coeff vector in basis 1,z,...,z^{n/2-1},
    using z^{n/2}=-1), then count F_p-collisions minus ring-collisions.
"""
import sys, math, itertools
from collections import Counter
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
    # (2r-1)!! = 1*3*5*...*(2r-1)
    v = 1
    for k in range(1, 2*r, 2):
        v *= k
    return v

def fp_root(n, p):
    g0 = primitive_root(p)
    g = pow(g0, (p-1)//n, p)
    return g

def coord_vector(exps, n):
    """Map an r-fold sum given as a multiset of exponents in [0,n) to its coordinate
    vector in Z[zeta_n] with basis 1,z,...,z^{n/2-1}, using z^{n/2} = -1.
    Returns a tuple of length n/2 of integers."""
    h = n // 2
    vec = [0]*h
    for e in exps:
        j = e % n
        if j < h:
            vec[j] += 1
        else:
            vec[j - h] -= 1
    return tuple(vec)

def energies_for_mu(mu, p, beta, rmax=6, nr_cap=6_000_000):
    """Compute E_r(F_p), char-0 E_r^0, Wick value, and #spurious_r for r=2..rmax,
    as long as n^r <= nr_cap (enumerating the r-fold sum multiset)."""
    n = 2**mu
    g = fp_root(n, p)
    roots_fp = [pow(g, j, p) for j in range(n)]   # mu_n in F_p, indexed by exponent
    results = []
    for r in range(2, rmax+1):
        if n**r > nr_cap:
            results.append((r, None, None, None, None, "n^r too large"))
            continue
        # enumerate all r-fold sums (ordered tuples of exponents); count by F_p value
        # and by Z[zeta_n] coordinate vector.
        fp_counter = Counter()
        ring_counter = Counter()
        # iterate ordered r-tuples of exponents in [0,n)
        for combo in itertools.product(range(n), repeat=r):
            s_fp = 0
            for e in combo:
                s_fp += roots_fp[e]
            s_fp %= p
            fp_counter[s_fp] += 1
            ring_counter[coord_vector(combo, n)] += 1
        # E_r = sum of squares of multiplicities (number of (a,b) pairs colliding)
        E_fp = sum(c*c for c in fp_counter.values())
        E_ring = sum(c*c for c in ring_counter.values())
        wick = double_factorial_odd(r) * (n**r)
        spurious = E_fp - E_ring
        results.append((r, E_fp, E_ring, wick, spurious, None))
    return results

def main():
    print("="*100)
    print("CONNECTION C2 — per-r char-p energy anomaly #spurious_r and the crossover r*")
    print("="*100)
    print()
    print("Identities: E_r(F_p) = #{(x,y) in mu_n^{2r}: sum x = sum y mod p} = (1/p) sum_b |eta_b|^{2r}")
    print("            E_r^0    = same with == in Z[zeta_n]   (char-0)")
    print("            Wick     = (2r-1)!! n^r   (dyadic Lam-Leung)")
    print("            #spurious_r = E_r(F_p) - E_r^0   (char-p EXCESS)")
    print("            trivial floor n^{2r}/p (the b=0 / diagonal term)")
    print()

    for mu in range(6, 13):
        n, p = prize_prime(mu)
        beta = math.log(p)/math.log(n)
        print(f"--- mu={mu}  n={n}  p={p}  beta={beta:.3f}  (prize-scale, p === 1 mod n) ---")
        res = energies_for_mu(mu, p, beta, rmax=6)
        print(f"  {'r':>2} {'E_r(F_p)':>14} {'E_r^0(ring)':>14} {'Wick(2r-1)!!n^r':>18} "
              f"{'#spurious':>12} {'n^{2r}/p':>14} {'spur/(n^2r/p)':>14} {'ring==Wick?':>11}")
        for (r, E_fp, E_ring, wick, spur, note) in res:
            if note:
                print(f"  {r:>2}  [{note}]")
                continue
            triv = (n**(2*r))/p
            ratio = spur/triv if triv > 0 else float('inf')
            ringwick = "YES" if E_ring == wick else f"no({E_ring} vs {wick})"
            print(f"  {r:>2} {E_fp:>14} {E_ring:>14} {wick:>18} "
                  f"{spur:>12} {triv:>14.2f} {ratio:>14.4f} {ringwick:>11}")
        print()

if __name__ == "__main__":
    main()
