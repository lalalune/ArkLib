#!/usr/bin/env python3
"""Falsifier + sharpness probe for the mod-p pair-sum rigidity weld (#357, vertical
stratum transfer surface).

Claims under test (PairSumRigidityModP.lean):
  (V1) RIGIDITY ABOVE THE THRESHOLD: for p prime with a primitive 2^k-th root g and
       p > 4^(2^(k-1)), any two distinct-element pairs {i,j} != {i',j'} (as sets) of
       exponents < 2^k with {i,j} non-antipodal (j != (i + 2^(k-1)) % 2^k) have
       g^i + g^j != g^i' + g^j'.
  (V2) FOLD FAITHFULNESS + CHAR-0 LAW: the folded 4-term integer polynomial
       R = fold(i) + fold(j) - fold(i') - fold(j') (fold t = +X^t if t < h else -X^(t-h),
       h = 2^(k-1)) is zero exactly when the pairs match ((i,j)=(i',j') or (i,j)=(j',i'))
       or BOTH pairs are antipodal (the excluded configuration).
  (V3) l1 mass of R is <= 4 and deg R < h (the threshold inputs).

Sharpness data: the largest prime actually exhibiting a violation, vs the threshold.
"""
from itertools import combinations

def isprime(m):
    if m < 2:
        return False
    d = 2
    while d * d <= m:
        if m % d == 0:
            return False
        d += 1
    return True

def violations_at_prime(p, n):
    """Return list of rigidity violations over F_p for mu_n, n = 2^k."""
    # find an element of multiplicative order exactly n
    g = None
    if (p - 1) % n != 0:
        return None
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1 for q in (2,)):
            g = cand
            break
    if g is None:
        return None
    h = n // 2
    pairs = [(i, j) for i, j in combinations(range(n), 2)]
    sums = {}
    out = []
    for (i, j) in pairs:
        s = (pow(g, i, p) + pow(g, j, p)) % p
        sums.setdefault(s, []).append((i, j))
    for s, ps in sums.items():
        if len(ps) > 1:
            for (a, b) in combinations(ps, 2):
                # violation iff at least one of the two pairs is non-antipodal
                anti = lambda q: (q[1] - q[0]) % n == h
                if not (anti(a) and anti(b)):
                    out.append((a, b, s))
    return out

def run_spectrum(k, pmax, expect_threshold):
    n = 1 << k
    bad_primes = []
    checked = 0
    for p in range(n + 1, pmax):
        if not isprime(p) or (p - 1) % n != 0:
            continue
        v = violations_at_prime(p, n)
        if v is None:
            continue
        checked += 1
        if v:
            bad_primes.append((p, len(v)))
    largest = max((p for p, _ in bad_primes), default=None)
    print(f"n={n}: checked {checked} primes < {pmax}; "
          f"violating primes: {bad_primes if len(bad_primes) < 12 else bad_primes[:12]}"
          f"{' ...' if len(bad_primes) >= 12 else ''}")
    print(f"n={n}: largest violating prime = {largest}, threshold 4^{n//2} = {expect_threshold}")
    assert largest is None or largest <= expect_threshold, (largest, expect_threshold)
    return largest

# V2: fold law in char 0
def fold_poly(n, i, j, ip, jp):
    h = n // 2
    coeff = [0] * h
    for t, sgn in ((i, 1), (j, 1), (ip, -1), (jp, -1)):
        if t < h:
            coeff[t] += sgn
        else:
            coeff[t - h] -= sgn
    return tuple(coeff)

def check_fold_law(k):
    n = 1 << k
    h = n // 2
    cnt_zero = 0
    for i, j in combinations(range(n), 2):
        for ip, jp in combinations(range(n), 2):
            R = fold_poly(n, i, j, ip, jp)
            matched = (i, j) == (ip, jp) or (i, j) == (jp, ip)
            both_anti = ((j - i) % n == h) and ((jp - ip) % n == h)
            l1 = sum(abs(c) for c in R)
            assert l1 <= 4, (i, j, ip, jp, l1)
            iszero = all(c == 0 for c in R)
            assert iszero == (matched or both_anti), (i, j, ip, jp, R, matched, both_anti)
            cnt_zero += iszero
    print(f"n={n}: V2 PASS — fold R = 0 iff matched-or-both-antipodal "
          f"({cnt_zero} zero tuples); V3 PASS — l1 <= 4 everywhere")

for k in (2, 3, 4):
    check_fold_law(k)

# V1 + sharpness. thresholds: n=8 -> 4^4 = 256; n=16 -> 4^8 = 65536.
run_spectrum(3, 2000, 256)
run_spectrum(4, 66000, 65536)
print("ALL PASS")
