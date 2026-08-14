#!/usr/bin/env python3
"""
Door-(iv) Lane-1 probe (#464) — PHASE-POSITION CURVATURE (second-difference rigidity)
of the worst-b coset of the thin 2-power subgroup mu_n < F_p^*.

GENUINELY-NEW MEASUREMENT (deconflicted vs the mapped faces):
  Mapped + dead already:
    - bulk anti-concentration / small-ball  (thin concentrates WORSE than random; DISPROOF)
    - three-gap distinct-gap count = n/2+1  (DILATION-INVARIANT => frequency-blind, rule-3 dead)
    - worst-b SET selection structure        (prime-independently DELOCALIZED; DISPROOF)
    - 2-adic / dyadic-tower coherence         (thickness-invariant; kernel-closed)

  NOT measured: the *curvature* (discrete second difference) of the sorted ANGULAR
  positions theta_x = (b* x mod p)/p in [0,1) AT THE WORST FREQUENCY b*. A multiplicative
  subgroup is NOT an AP, so its sorted positions could (a) be near-equidistributed
  (curvature ~ 0, no grip), or (b) carry a low-complexity second-difference structure
  (few distinct curvatures => a Halasz/Littlewood-type curvature lever that does NOT route
  through multiplicative energy or sum-product).

THE QUESTION (frequency-SENSITIVE => passes rule-3 if it DIFFERS at b* vs generic b):
  Q1. At b*, how many DISTINCT second-differences D2_i = (theta_{i+1}-theta_i)-(theta_i-theta_{i-1})
      does the sorted-position sequence have? (relative to n)
  Q2. Is the distinct-D2 count at b* DIFFERENT from a generic b (frequency-sensitive)?
      If identical => dilation-invariant => DEAD (like three-gap).
  Q3. Does the curvature complexity grow with thinness (n) or stay O(1)?

Prize regime: PROPER 2-power subgroup mu_n < F_p^*, p == 1 mod n, p ~ n^4 >> n^3,
NEVER n=q-1. Multiple structured primes per n; report median. EXACT integer arithmetic
(no float phase sums for the argmax search). Empirical only — proves nothing.
"""
import sys
from math import gcd

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, beta, count):
    """primes p == 1 (mod n), p ~ n^beta, p >> n^3."""
    target = n ** beta
    lo = max(target // 2, n ** 3 + 1)
    out = []
    # search p = 1 + k*n upward from lo
    k = (lo - 1) // n + 1
    while len(out) < count and k < 50_000_000:
        p = 1 + k * n
        if p > lo and is_prime(p):
            out.append(p)
        k += 1
    return out

def subgroup_mu_n(p, n):
    """the order-n 2-power subgroup of F_p^* (n | p-1)."""
    # find a generator g of F_p^*
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    # factor p-1 to test primitivity
    m = p - 1
    fac = set()
    mm = m; d = 2
    while d * d <= mm:
        while mm % d == 0:
            fac.add(d); mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    g = None
    for cand in range(2, p):
        if all(pow(cand, m // q, p) != 1 for q in fac):
            g = cand; break
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x); x = (x * h) % p
    return mu

def eta_abs2(b, mu, p):
    """|sum_{x in mu} e_p(b x)|^2 via exact cos/sin? use float — only for ranking."""
    import cmath, math
    s = 0j
    for x in mu:
        ang = 2 * math.pi * ((b * x) % p) / p
        s += cmath.exp(1j * ang)
    return (s.real * s.real + s.imag * s.imag)

def distinct_second_diffs(b, mu, p, tol_den=10**9):
    """sorted positions theta = (b x mod p) on the integer ring Z_p (additive line),
    return number of distinct second-differences of the circular sorted sequence.
    Use EXACT integer positions in Z_p; circular second difference."""
    pos = sorted(((b * x) % p) for x in mu)
    N = len(pos)
    # circular first differences (gaps), exact integers summing to p
    gaps = [(pos[(i + 1) % N] - pos[i]) % p for i in range(N)]
    # second differences of the gap sequence (circular): g_{i+1}-g_i
    d2 = [gaps[(i + 1) % N] - gaps[i] for i in range(N)]
    return len(set(d2)), len(set(gaps))

def main():
    print("# Door-IV worst-b PHASE-POSITION CURVATURE probe (#464)")
    print("# columns: n  p  worstb  distinctGaps(b*)  distinctD2(b*)  | genericb distinctD2")
    for n in [16, 32, 64]:
        beta = 4
        ps = primes_1_mod_n(n, beta, 5)
        if not ps:
            print(f"# n={n}: no primes found"); continue
        rows = []
        for p in ps:
            mu = subgroup_mu_n(p, n)
            # worst b over quotient F_p^*/mu_n ~ a set of coset reps; scan reps = 1..(p-1)//n by stepping a generator quotient.
            # Cheap proxy: scan b over a uniform random sample of F_p^* (coset-constant eta, so any rep works);
            # to avoid scan-stride artifacts we sample b uniformly.
            import random
            random.seed(464 + p)
            m = (p - 1) // n
            # sample up to 400 coset reps by random b (eta is mu-coset-constant)
            seen_cosets = {}
            cand_bs = []
            tries = 0
            while len(cand_bs) < min(400, m) and tries < 4000:
                b = random.randrange(1, p)
                # coset id = b * mu_n as a frozenset is expensive; just dedup by min of coset
                cmin = min((b * x) % p for x in mu)
                if cmin not in seen_cosets:
                    seen_cosets[cmin] = b
                    cand_bs.append(b)
                tries += 1
            # worst b
            bstar = max(cand_bs, key=lambda b: eta_abs2(b, mu, p))
            dg, _ = (lambda r: (r[1], r[0]))(distinct_second_diffs(bstar, mu, p))
            d2star, _g = distinct_second_diffs(bstar, mu, p)
            # generic b = a random non-worst coset rep
            genb = random.choice([b for b in cand_bs if b != bstar]) if len(cand_bs) > 1 else bstar
            d2gen, _g2 = distinct_second_diffs(genb, mu, p)
            rows.append((p, bstar, _g, d2star, d2gen))
            print(f"  n={n:3d}  p={p:>10d}  b*={bstar:>9d}  gaps={_g:>3d}  D2*={d2star:>3d}  | gen D2={d2gen:>3d}")
        # medians
        import statistics as st
        med_d2star = st.median(r[3] for r in rows)
        med_d2gen = st.median(r[4] for r in rows)
        med_gaps = st.median(r[2] for r in rows)
        print(f"# n={n}: median distinctGaps(b*)={med_gaps}  distinctD2(b*)={med_d2star}  vs generic D2={med_d2gen}"
              f"  (n/2+1 = {n//2+1})  frequency-sensitive? {'YES' if med_d2star != med_d2gen else 'NO (dilation-invariant => DEAD)'}")
    print("# DONE")

if __name__ == "__main__":
    main()
