#!/usr/bin/env python3
"""
Probe for Door-IV variance-core trivial envelope.

Checks proper thin subgroups mu_n < F_p^* with p >> n^3.  For sample relation sets made from
zero-sum r-tuples in mu_n, verifies:
  |Jphase(T)| = 1,
  |sum_T Jphase(T)| <= #Rel,
  norm_sq(sum_T Jphase(T)) <= #Rel^2,
  DiffTrace.re = norm_sq(sum) - #Rel <= #Rel^2 - #Rel.
This is only the triangle envelope, not a cancellation claim.
"""
from __future__ import annotations

import cmath
import math
from itertools import product


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def next_prime_congruent_one(start: int, n: int) -> int:
    p = max(3, start | 1)
    while True:
        if p % n == 1 and is_prime(p):
            return p
        p += 2


def primitive_root(p: int) -> int:
    factors = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            factors.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def subgroup_mu(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    z = pow(g, (p - 1) // n, p)
    vals = []
    x = 1
    for _ in range(n):
        vals.append(x)
        x = (x * z) % p
    return sorted(vals)


def jphase(p: int, tup: tuple[int, ...]) -> complex:
    s = sum(tup) % p
    phase_sum = sum(tup) - s  # not used; product form below is additive-char normalized
    prod_phase = sum(tup) - s
    # theta(a)=exp(2pi i a/p); prod theta(x_i)*conj theta(sum x_i)
    return cmath.exp(2j * math.pi * ((sum(tup) - s) % p) / p)


def run_case(n: int, beta: float, r: int) -> dict[str, float | int]:
    p = next_prime_congruent_one(int(n ** beta), n)
    mu = subgroup_mu(p, n)
    assert len(mu) == n and n < p - 1
    # Keep relation count bounded: enumerate prefixes and solve final coordinate in mu.
    muset = set(mu)
    rel = []
    cap = 20000
    for pref in product(mu, repeat=r - 1):
        need = (-sum(pref)) % p
        if need in muset:
            rel.append(pref + (need,))
            if len(rel) >= cap:
                break
    vals = [jphase(p, T) for T in rel]
    m = len(vals)
    z = sum(vals)
    max_unit_err = max((abs(abs(v) - 1.0) for v in vals), default=0.0)
    norm = abs(z)
    norm_sq = norm * norm
    diff_re = norm_sq - m
    return {
        "n": n,
        "beta_x10": int(round(beta * 10)),
        "p": p,
        "r": r,
        "rel": m,
        "unit_err": max_unit_err,
        "norm_minus_card": norm - m,
        "normsq_minus_card2": norm_sq - m * m,
        "diff_minus_ceiling": diff_re - (m * m - m),
    }


def main() -> None:
    cases = []
    for n in (16, 32, 64):
        for beta in (4.0, 4.5):
            for r in (3, 4, 5):
                cases.append(run_case(n, beta, r))
    worst = {k: max(abs(c[k]) for c in cases) for k in ("unit_err",)}
    print("Door-IV DiffTrace trivial-envelope probe (proper mu_n, p>>n^3, never full group)")
    for c in cases:
        print(c)
        assert c["unit_err"] < 1e-12
        assert c["norm_minus_card"] <= 1e-8
        assert c["normsq_minus_card2"] <= 1e-6
        assert c["diff_minus_ceiling"] <= 1e-6
    print("PASS", worst)


if __name__ == "__main__":
    main()
