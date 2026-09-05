#!/usr/bin/env python3
"""Exact subgroup specialization checks; no Paley conjecture is assumed."""

import json
from math import isqrt, log, sqrt

P = 365375409332725729550921208179070755120141565953
N = 2**30


def quadratic(x, p):
    value = pow(x % p, (p-1)//2, p)
    return -1 if value == p-1 else value


def check(p, n):
    assert p > 2 and all(p % d for d in range(2, isqrt(p)+1))
    assert (p-1) % n == 0 and n & (n-1) == 0
    generator = next(g for base in range(2, p)
                     if pow(g := pow(base, (p-1)//n, p), n//2, p) != 1)
    subgroup = [pow(generator, j, p) for j in range(n)]
    assert len(set(subgroup)) == n
    character_mass = sum(quadratic(x, p) for x in subgroup)
    maximum = 0
    for shift in range(1, p):
        single = sum(quadratic(1+shift*x, p) for x in subgroup)
        double = sum(quadratic(a+shift*b, p)
                     for a in subgroup for b in subgroup)
        assert double == character_mass*single
        maximum = max(maximum, abs(single))
    if character_mass == 0:
        # Omitting the character-triviality hypothesis would incorrectly
        # identify this zero double sum with n times a nonzero single sum.
        single = sum(quadratic(1+x, p) for x in subgroup)
        double = sum(quadratic(a+b, p) for a in subgroup for b in subgroup)
        assert double == 0 and single == -1 and double != n*single
    return {"p": p, "n": n, "character_mass": character_mass,
            "shifts_checked": p-1, "max_abs_shifted_sum": maximum}


def main():
    assert P == N*(2**128+192)+1
    assert N**4 < P and N**5 < P < N**6
    assert N**50 > P**9  # N > P^(9/50), using exact integer arithmetic.
    assert ((P-1)//N) % 2 == 0  # The production subgroup lies in the squares.
    for p, n in ((17, 4), (97, 8), (257, 16), (17, 16)):
        print(json.dumps(check(p, n), sort_keys=True))
    logarithm = log(P/N)
    print(json.dumps({"production_n": N, "production_p": P,
        "index": (P-1)//N, "below_fourth_root": True,
        "above_p_to_9_over_50": True,
        "approx_log_p_n": log(N)/log(P),
        "approx_unit_constant_sqrt_n_log_index": sqrt(N*logarithm),
        "approx_delta_needed_for_shifted_target_C1":
            log(N/logarithm)/(2*log(P)),
        "scope": "Exact identities and size gates; logarithmic values are approximations."},
        sort_keys=True))


if __name__ == "__main__":
    main()
