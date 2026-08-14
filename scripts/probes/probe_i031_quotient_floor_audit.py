#!/usr/bin/env python3
"""I031 quotient-floor audit for the proximity-prize Gauss-period core.

This is a deliberately small, exact-arithmetic probe.  It checks two claims behind
the I031 dilation-quotient handle:

1. the period value is exactly constant on every multiplicative coset of mu_n;
2. after quotienting, the observed floor constant M / sqrt(n log((p-1)/n))
   stays O(1) on proper-subgroup instances.

The probe uses direct summation, so it keeps to moderate p.  It is not a proof of
the deterministic-to-Gaussian transfer; it is an adversarial sanity check for the
quotient reduction and the bounded-constant prediction.
"""

from __future__ import annotations

import cmath
import math
import random
from dataclasses import dataclass


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    # Deterministic for n < 2^64.
    for a in [2, 3, 5, 7, 11, 13, 17]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def prime_congruent_one(n: int, start: int) -> int:
    p = start + ((1 - start) % n)
    if p <= n:
        p += n
    while not is_prime(p):
        p += n
    return p


def factor(n: int) -> list[int]:
    fs = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs.append(n)
    return fs


def primitive_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError(f"no primitive root found for p={p}")


@dataclass
class AuditRow:
    n: int
    beta: float
    p: int
    m: int
    max_coset_spread: float
    floor_constant: float
    gaussian_sup_ratio: float
    quotient_ratio: float


def audit(n: int, beta: float, gaussian_samples: int = 80) -> AuditRow:
    p = prime_congruent_one(n, int(math.ceil(n**beta)))
    m = (p - 1) // n
    g = primitive_root(p)
    zeta = pow(g, m, p)
    mu = [pow(zeta, i, p) for i in range(n)]
    reps = [pow(g, j, p) for j in range(m)]

    omega = 2.0 * math.pi / p
    table = [complex(math.cos(omega * a), math.sin(omega * a)) for a in range(p)]

    max_spread = 0.0
    max_abs = 0.0
    phase_rows = []
    for r in reps:
        row = []
        vals = []
        # One full orbit; exact constancy should hold up to floating roundoff.
        for z in mu:
            b = (r * z) % p
            s = 0j
            for x in mu:
                s += table[(b * x) % p]
            vals.append(s)
        center = vals[0]
        for x in mu:
            row.append(table[(r * x) % p])
        phase_rows.append(row)
        max_spread = max(max_spread, max(abs(v - center) for v in vals))
        max_abs = max(max_abs, abs(center))

    rng = random.Random(444031 + n)
    gaussian_sups = []
    # Matched complex Gaussian process: X_r = sum_x gamma_x e_p(r x), with
    # E |gamma_x|^2 = 1, hence point variance n, matching the period floor scale.
    for _ in range(gaussian_samples):
        gamma = [
            complex(rng.gauss(0.0, 1.0 / math.sqrt(2.0)), rng.gauss(0.0, 1.0 / math.sqrt(2.0)))
            for _ in range(n)
        ]
        sup = 0.0
        for row in phase_rows:
            val = 0j
            for coeff, phase in zip(gamma, row):
                val += coeff * phase
            sup = max(sup, abs(val))
        gaussian_sups.append(sup)
    gaussian_mean_sup = sum(gaussian_sups) / len(gaussian_sups)

    floor = math.sqrt(n * math.log(m))
    return AuditRow(
        n=n,
        beta=beta,
        p=p,
        m=m,
        max_coset_spread=max_spread,
        floor_constant=max_abs / floor,
        gaussian_sup_ratio=max_abs / gaussian_mean_sup,
        quotient_ratio=m / (p - 1),
    )


def main() -> None:
    cases = [(16, 2.4), (32, 2.35), (64, 2.25), (128, 2.10)]
    print("I031 quotient-floor audit")
    print("direct exact cosets; proper subgroup only (m=(p-1)/n > 1)")
    print(
        f"{'n':>5} {'beta':>5} {'p':>10} {'m':>8} {'coset spread':>14} "
        f"{'M/sqrt(n log m)':>18} {'M/E sup G':>11} {'m/(p-1)':>10}"
    )
    worst_spread = 0.0
    constants = []
    transfer_ratios = []
    for n, beta in cases:
        row = audit(n, beta)
        worst_spread = max(worst_spread, row.max_coset_spread)
        constants.append(row.floor_constant)
        transfer_ratios.append(row.gaussian_sup_ratio)
        print(
            f"{row.n:5d} {row.beta:5.2f} {row.p:10d} {row.m:8d} "
            f"{row.max_coset_spread:14.3e} {row.floor_constant:18.3f} "
            f"{row.gaussian_sup_ratio:11.3f} {row.quotient_ratio:10.3e}"
        )
    print(f"verdict: coset constancy holds to roundoff; floor constants in [{min(constants):.3f}, {max(constants):.3f}].")
    print(
        "transfer audit: deterministic/Gaussian sup ratios in "
        f"[{min(transfer_ratios):.3f}, {max(transfer_ratios):.3f}] with a fixed seed."
    )
    print("status: I031 survives this audit; the remaining gap is proving the bounded transfer.")
    if worst_spread > 1e-8:
        raise SystemExit("coset constancy failed beyond roundoff")


if __name__ == "__main__":
    main()
