#!/usr/bin/env python3
"""
#407 CONNECTION C2 (DECISIVE) — per-moment char-p anomaly, the crossover r*, and
whether the COUNT-LANE worst-case r sits BELOW or ABOVE that crossover.

================================================================================
THE TWO DISTINCT "r"s (the heart of C2 — must not be conflated)
================================================================================

(A) MOMENT depth r  (the BGK / sup-norm route):
      E_r(F_p) = #{(x,y) in mu_n^{2r} : sum x_i = sum y_j (mod p)}
               = (1/p) * sum_{b=0}^{p-1} |eta_b|^{2r},   eta_b = sum_{x in mu_n} e_p(b x).
      char-0 (Z[zeta_n]) value: E_r^0 = #{(x,y): sum x = sum y in the ring}.
      For dyadic mu_n this equals the Wick value (2r-1)!! n^r in the *non-saturated*
      reading, but we compute E_r^0 DIRECTLY (ring collisions) to be exact.
      ANOMALY:  #spurious_r := E_r(F_p) - E_r^0   (>= 0 always, Fourier-positive).
      The sup-norm M = max_{b!=0}|eta_b| is read off as M ~ (p * A_r)^{1/2r},
      A_r = E_r(F_p) - n^{2r}/p; extracting M needs r -> infinity.
      CROSSOVER r*: the moment depth at which #spurious_r becomes Theta(n^{2r}/p),
      i.e. the char-p excess stops being negligible vs the trivial diagonal floor.

(B) CONFIG-SIZE r  (the count lane that pins delta* directly):
      delta* is set by the WORST-CASE agreement set, whose size is
      |S| = r*m ~ rho * n  (rho = the rate; the agreement length is a FIXED
      fraction of n, NOT a limit r->infinity). So the count lane uses ONE r:
          r_count = (rho * n) / m   (a single, finite, rate-determined depth).
      N0 = #bad = #{distinct e_m(S) : S size r*m, e_i(S)=0 for i in gap}.
      This is q-INDEPENDENT iff no char-p-spurious non-coset S contributes a new e_m.

THE C2 QUESTION (b):  is r_count  <  r*  (count lane is char-0/clean, BGK bypassed)
                       or r_count  >  r*  (count lane re-hits the moment wall)?

================================================================================
What this probe computes
================================================================================
PART 1 (moment anomaly + crossover r*):
  For n=2^mu (mu = 6..10, capped by feasibility) at prize prime p ~ n^4:
  #spurious_r = E_r(F_p) - E_r^0(ring) for r = 2,3,4,...  via convolution
  (ring lattice = small support; F_p via convolution too but we use the
   EXACT cheap method: build the r-fold sum multiset by exponent and compare
   F_p-value collisions vs ring-coordinate collisions).
  Report #spurious_r, n^{2r}/p, the ratio, and flag the first r with ratio >= 1.
  Compare measured r* to beta+1.

PART 2 (the count-lane r):
  r_count = rho * n / m for prize rate rho ~ 1/2 .. and m=2 (the live m).
  Print r_count for mu=6..30 and put it next to r* (= beta+1 ~ 5).

PART 3 (does worst-case-r for the COUNT exceed r*? — direct test):
  For small n we directly measure, as a function of config-size r, whether ANY
  char-p-spurious (non-coset) valid config exists at a NON-SATURATED prime.
  The 'count crossover' is the smallest r at which a spurious config first
  appears at a non-saturated prime. Compare to the moment r*.
"""
import sys, math, itertools
from collections import Counter, defaultdict
from sympy import isprime, primitive_root
from math import comb

# ----------------------------------------------------------------------------
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

def coord_vector(exps, n):
    """r-fold sum (multiset of exponents) -> Z[zeta_n] coord vector len n/2 (z^{n/2}=-1)."""
    h = n // 2
    vec = [0]*h
    for e in exps:
        j = e % n
        if j < h: vec[j] += 1
        else:     vec[j - h] -= 1
    return tuple(vec)

# ----------------------------------------------------------------------------
# PART 1: moment anomaly via convolution.
#   ring distribution: support is the coord lattice (small); convolution cheap.
#   F_p distribution:  we DON'T need the full Z/p convolution. Key trick:
#     #spurious_r = (#F_p collisions) - (#ring collisions).  Two distinct
#     ring-coordinate vectors collide in F_p iff their DIFFERENCE maps to 0 in F_p,
#     i.e. the integer-coord difference vector d satisfies sum_j d_j * g^j ≡ 0 (p).
#     So #spurious_r = sum over PAIRS of distinct ring-classes (a,b) of
#        mult(a)*mult(b)  for which a-b -> 0 in F_p.
#   We therefore enumerate the ring distribution (coord -> multiplicity), then
#   for the F_p side bucket coords by their F_p image; collisions across distinct
#   ring-classes within one F_p bucket are exactly the spurious pairs.
# ----------------------------------------------------------------------------
def moment_anomaly(mu, p, rmax, ring_support_cap=8_000_000):
    n = 2**mu
    h = n // 2
    g = fp_root(n, p)
    # F_p image of coord vector: sum_j c_j * g^j  (mod p)
    gpow = [pow(g, j, p) for j in range(h)]
    # 1-fold ring distribution: each root j -> coord vec, multiplicity 1
    root_vecs = []
    for j in range(n):
        v = [0]*h
        if j < h: v[j] += 1
        else:     v[j-h] -= 1
        root_vecs.append(tuple(v))
    ring = defaultdict(int)
    for v in root_vecs: ring[v] += 1
    out = {}
    cur = dict(ring)   # dist_1 (ring coords)
    for r in range(1, rmax+1):
        if r >= 2:
            if len(cur) > ring_support_cap:
                out[r] = (None, None, "ring support too large")
            else:
                E_ring = sum(c*c for c in cur.values())
                # F_p collisions: bucket coords by F_p image
                fp_bucket = defaultdict(int)   # image -> total multiplicity
                for coord, c in cur.items():
                    img = 0
                    for j, cj in enumerate(coord):
                        if cj: img = (img + cj*gpow[j]) % p
                    fp_bucket[img] += c
                E_fp = sum(c*c for c in fp_bucket.values())
                spurious = E_fp - E_ring
                out[r] = (E_fp, E_ring, spurious)
        if r == rmax: break
        # convolve ring dist by 1-fold
        if len(cur) > ring_support_cap:
            for rr in range(r+1, rmax+1): out[rr] = (None,None,"ring support too large")
            break
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rv in root_vecs:
                nxt[tuple(a+b for a,b in zip(v,rv))] += c
        cur = nxt
    return out

# ----------------------------------------------------------------------------
# PART 3: count-lane spurious appearance vs config size r, at a NON-SATURATED prime.
#   For m=2: gap indices {1,3}; valid S of size 2r has e1(S)=e3(S)=0.
#   spurious = a valid S that is NOT a union of mu_2-cosets (i.e. not +/- paired)
#              -> contributes a possibly-new e_2.
#   We enumerate size-2r subsets of mu_n (n small) and test at a non-saturated prime.
# ----------------------------------------------------------------------------
def count_lane_spurious(n, rmax_cfg, p):
    """Return, per config-size r (so |S|=2r), the number of NON-COSET valid configs
    at prime p (m=2). Non-saturated p assumed (caller picks)."""
    h = n//2
    g = fp_root(n, p)
    roots = [pow(g, j, p) for j in range(n)]
    res = {}
    for r in range(2, rmax_cfg+1):
        size = 2*r
        if comb(n, size) > 3_000_000:
            res[r] = (None, None, "too many subsets")
            continue
        valid = 0; noncoset = 0
        e2vals = set()
        for S in itertools.combinations(range(n), size):
            pts = [roots[j] for j in S]
            # e1 = sum, e3 = 3rd elementary symmetric, mod p
            e1 = sum(pts) % p
            if e1 != 0: continue
            # e3
            e3 = 0
            for c3 in itertools.combinations(pts, 3):
                e3 = (e3 + c3[0]*c3[1]*c3[2]) % p
            if e3 != 0: continue
            valid += 1
            # coset test: is S a union of mu_2 cosets? exponents pair j <-> j+h
            expset = set(S)
            is_coset = all(((j + h) % n) in expset for j in S)
            if not is_coset:
                noncoset += 1
            # e2 value
            e2 = 0
            for c2 in itertools.combinations(pts, 2):
                e2 = (e2 + c2[0]*c2[1]) % p
            e2vals.add(e2)
        res[r] = (valid, noncoset, len(e2vals))
    return res, g

# ----------------------------------------------------------------------------
def main():
    print("="*100)
    print("CONNECTION C2 DECISIVE — moment crossover r* vs count-lane r")
    print("="*100)

    # -------- PART 1 --------
    print("\n### PART 1: MOMENT anomaly  #spurious_r = E_r(F_p) - E_r^0(ring),  prize p~n^4")
    print("    crossover r* = first r with  #spurious_r / (n^{2r}/p)  >= 1  (excess non-negligible)\n")
    for mu in [6, 7, 8, 9, 10]:
        n, p = prize_prime(mu)
        beta = math.log(p)/math.log(n)
        # ring support grows ~ (r*h) coords; cap r by feasibility
        rmax = 6 if mu <= 7 else (5 if mu <= 8 else 4)
        out = moment_anomaly(mu, p, rmax)
        print(f"--- mu={mu} n={n} p={p} beta={beta:.3f}  (beta+1={beta+1:.2f})  rmax={rmax} ---")
        print(f"  {'r':>2} {'E_r(F_p)':>16} {'E_r^0(ring)':>16} {'#spurious':>12} "
              f"{'Wick':>16} {'ring=Wick?':>10} {'n^2r/p':>14} {'spur/(n2r/p)':>13} {'crossover?':>10}")
        r_star = None
        for r in range(2, rmax+1):
            Efp, Erg, spur = out.get(r, (None,None,None))
            wick = double_factorial_odd(r)*(n**r)
            triv = (n**(2*r))/p
            if Efp is None:
                print(f"  {r:>2} {'(cap)':>16}")
                continue
            ratio = spur/triv if triv>0 else float('inf')
            rw = "YES" if Erg==wick else "no"
            cross = ""
            if ratio >= 1 and r_star is None:
                r_star = r; cross = "<< r*"
            print(f"  {r:>2} {Efp:>16} {Erg:>16} {spur:>12} {wick:>16} {rw:>10} "
                  f"{triv:>14.2f} {ratio:>13.6f} {cross:>10}")
        print(f"  measured r* (moment crossover) = {r_star}   vs beta+1 = {beta+1:.2f}\n")

    # -------- PART 2 --------
    print("\n### PART 2: COUNT-LANE depth  r_count = rho*n/m  (single, rate-fixed)  vs  r* ~ beta+1 ~ 5")
    print("    prize rate rho ~ 1/2 (window edge), m=2 (live coset modulus)\n")
    print(f"  {'mu':>3} {'n':>10} {'r*=beta+1':>10} {'r_count(rho=1/2,m=2)':>22} {'r_count(rho=1/4)':>18} {'r_count >> r* ?':>16}")
    for mu in range(6, 31):
        n = 2**mu
        # prize prime ~ n^4 -> beta=4 -> r*~5; r_count = rho*n/m
        rstar = 5.0
        rc_half = 0.5*n/2
        rc_quart = 0.25*n/2
        flag = "YES (r_count >> r*)" if rc_half > rstar else "no"
        print(f"  {mu:>3} {n:>10} {rstar:>10.1f} {rc_half:>22.1f} {rc_quart:>18.1f} {flag:>16}")

    # -------- PART 3 --------
    print("\n### PART 3: COUNT-LANE spurious onset vs config-size r at a NON-SATURATED prime (m=2)")
    print("    smallest config-r at which a NON-COSET valid config appears (non-saturated p)\n")
    for n in [8, 16, 24, 32]:
        # pick a moderately large non-saturated prime p === 1 mod n
        p = None
        cand = max(2003, n*50)
        cand = cand - (cand % n) + 1
        while True:
            if isprime(cand): p = cand; break
            cand += n
        # ensure non-saturated: |Sigma_r| ~ n^r/(2^r r!) << p for the r we test
        res, g = count_lane_spurious(n, 5, p)
        beta = math.log(p)/math.log(n)
        print(f"  n={n} p={p} (beta={beta:.2f}, non-saturated):")
        for r in sorted(res):
            valid, noncoset, ne2 = res[r]
            if valid is None:
                print(f"    r={r} |S|={2*r}: {res[r][2]}")
                continue
            tag = "  <-- SPURIOUS (non-coset valid)" if noncoset and noncoset>0 else "  (all cosets)"
            print(f"    r={r} |S|={2*r}: valid_configs={valid} noncoset={noncoset} distinct_e2={ne2}{tag}")
    print()

if __name__ == "__main__":
    main()
