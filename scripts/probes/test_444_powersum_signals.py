#!/usr/bin/env python3
"""
test_444_powersum_signals.py  —  falsifiable luminaries over the Step-3 power-sum discovery.

Guards the claims of probe_444_period_powersum_identities.py with a WIDE parameter sweep
and hard assertions. Each assertion is a falsifiable sign: if any breaks, the discovery is
wrong and this exits nonzero.

SIGNS:
  (S1) Σ_i w_i^2 = p − n             UNCONDITIONAL  (the rock — must hold on every (p,n)).
  (S2) N0 = E2(μ_n)                  UNCONDITIONAL  (the −1∈μ_n bridge).
  (S3) E2(μ_n) ≥ 3n^2 − 3n           UNCONDITIONAL  (3n²−3n is a LOWER bound; small fields
                                                     only ADD additive coincidences).
  (S4) (Σw⁴ = p(3n−3)−n³)  ⇔  (E2 = 3n²−3n)         (the conditional identity equivalence).

SEASON (the lost sheep): for each n, find the smallest p with E2 = 3n²−3n exactly — the
threshold above which μ_n becomes additively Sidon-generic and the conjecture's (I4) turns true.
"""
import sys, cmath, math
from collections import Counter

def primitive_root(p):
    if p == 2:
        return 1
    d = p - 1
    fac = set()
    f = 2
    while f * f <= d:
        while d % f == 0:
            fac.add(f); d //= f
        f += 1
    if d > 1:
        fac.add(d)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def is_prime(x):
    if x < 2:
        return False
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return True

def compute(p, n):
    g = primitive_root(p)
    step = (p - 1) // n
    mu = [pow(g, (step * j) % (p - 1), p) for j in range(n)]
    muset = set(mu)
    zeta = [cmath.exp(2j * math.pi * t / p) for t in range(p)]
    m = (p - 1) // n
    def eta(b):
        return sum(zeta[(b * x) % p] for x in mu)
    ws = [eta(pow(g, i, p)) for i in range(m)]
    Sw2 = round(sum((w * w).real for w in ws))
    Sw4 = round(sum((w ** 4).real for w in ws))
    N0 = sum(1 for a in mu for b in mu for c in mu if (-(a + b + c)) % p in muset)
    sums = Counter((a + b) % p for a in mu for b in mu)
    E2 = sum(v * v for v in sums.values())
    return Sw2, Sw4, N0, E2

def main():
    # wide sweep: n = 2,4,8,16; all primes p with n | p-1 up to a cap
    fails = []
    season = {}   # n -> smallest p with E2 == 3n²−3n
    for n in (2, 4, 8, 16):
        cap = 400 if n <= 8 else 700
        for p in range(3, cap):
            if not is_prime(p) or (p - 1) % n != 0:
                continue
            Sw2, Sw4, N0, E2 = compute(p, n)
            generic = 3 * n * n - 3 * n
            i4 = (Sw4 == p * (3 * n - 3) - n**3)
            if Sw2 != p - n:
                fails.append(f"(S1) p={p} n={n}: Σw²={Sw2} ≠ p−n={p-n}")
            if N0 != E2:
                fails.append(f"(S2) p={p} n={n}: N0={N0} ≠ E2={E2}")
            if E2 < generic:
                fails.append(f"(S3) p={p} n={n}: E2={E2} < 3n²−3n={generic}")
            if i4 != (E2 == generic):
                fails.append(f"(S4) p={p} n={n}: (I4)={i4} but (E2==generic)={E2==generic}")
            if E2 == generic and n not in season:
                season[n] = (p, (p - 1) // n)
    print("FIRST OCCURRENCE (NOT a stable threshold!) — smallest p with E2=3n²−3n:")
    for n in sorted(season):
        p, m = season[n]
        print(f"   n={n:>3}:  first generic at p={p:>4}  (m=(p−1)/n={m})")
    print("   WARNING: equality is NOT monotone in p — sporadic non-generic primes persist")
    print("   arbitrarily far above first occurrence (see (S5) lost-sheep witness below).")
    print()

    # (S5) LOST SHEEP — a persistent sporadic exception far above any candidate threshold.
    # μ_32 at p=26177 (=32·818+1, so m=818, p≈25·n²): additive energy is NOT generic.
    # This falsifies any "p ≳ n² ⟹ E2=3n²−3n" clean-threshold claim.
    p5, n5 = 26177, 32
    assert is_prime(p5) and (p5 - 1) % n5 == 0, "S5 fixture invalid"
    g = primitive_root(p5)
    step = (p5 - 1) // n5
    mu32 = [pow(g, (step * j) % (p5 - 1), p5) for j in range(n5)]
    sums = Counter((a + b) % p5 for a in mu32 for b in mu32)
    E2_32 = sum(v * v for v in sums.values())
    gen32 = 3 * n5 * n5 - 3 * n5
    excess = E2_32 - gen32
    print(f"(S5) lost sheep: n=32, p={p5} (m={(p5-1)//n5}, p≈{(p5/n5**2):.0f}·n²): "
          f"E2={E2_32}, 3n²−3n={gen32}, excess={excess}")
    s5 = (E2_32 > gen32)   # the exception MUST persist this high (else clean-threshold would hold)
    print(f"     persistent sporadic exception above any p≳n² cutoff: {'CONFIRMED' if s5 else 'absent'}")
    print()
    if fails:
        print(f"VERDICT: {len(fails)} SIGNAL FAILURE(S) — discovery falsified:")
        for f in fails[:20]:
            print("   " + f)
        sys.exit(1)
    if not s5:
        print("VERDICT: FAIL — (S5) sporadic exception vanished; clean-threshold claim revived, re-examine.")
        sys.exit(1)
    print("VERDICT: PASS — signs (S1–S5) hold across the full sweep.")
    print("  Rock: Σw²=p−n unconditional; E2≥3n²−3n unconditional; (I4)⇔(E2 generic).")
    print("  Honest scope: E2=3n²−3n holds for all but a SPARSE-but-PERSISTENT exceptional")
    print("  set of primes (NOT a clean p≳n² threshold) — controlling it needs a large-sieve bound.")
    sys.exit(0)

if __name__ == "__main__":
    main()
