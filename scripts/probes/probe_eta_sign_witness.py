#!/usr/bin/env python3
"""Extract an EXPLICIT small counterexample to s_b being multiplicative, for a Lean-decidable brick.
We want concrete (p, n, b1, b2) with s_{b1}=s_{b2}=+1 but s_{b1 b2} = -1 (or any product mismatch),
at a SMALL prime so the witness is checkable. Also report the integer sign of eta for a few b
(eta_b is a real algebraic integer; its sign is what we formalize as non-multiplicative).
"""
import numpy as np


def subgroup(p, n):
    # primitive root brute for small p
    def gen(p):
        for g in range(2, p):
            seen = set()
            v = 1
            for _ in range(p - 1):
                seen.add(v)
                v = v * g % p
            if len(seen) == p - 1:
                return g
        return None
    g = gen(p)
    h = pow(g, (p - 1) // n, p)
    s = set()
    v = 1
    for _ in range(n):
        s.add(v)
        v = v * h % p
    return sorted(s), g


def eta(p, mu, b):
    z = 2j * np.pi / p
    return sum(np.exp(z * (b * x % p)) for x in mu).real


def sgn(x):
    return 1 if x > 1e-9 else (-1 if x < -1e-9 else 0)


# small thin example: n=4, p=89 (p-1=88=8*11, mu_4 proper, p>>n^3=64)
for (p, n) in [(89, 4), (257, 4), (113, 4)]:
    mu, g = subgroup(p, n)
    print(f"\np={p} n={n} mu_n={mu} (gen={g})")
    signs = {}
    for b in range(1, p):
        signs[b] = sgn(eta(p, mu, b))
    # print sign per coset rep
    seen = set()
    reps = []
    for b in range(1, p):
        cb = frozenset((b * x) % p for x in mu)
        if cb not in seen:
            seen.add(cb)
            reps.append(b)
    print("coset reps + signs:", [(b, signs[b]) for b in reps])
    # find a multiplicative violation among reps
    found = None
    for b1 in reps:
        for b2 in reps:
            bp = (b1 * b2) % p
            if signs[b1] and signs[b2] and signs[bp]:
                if signs[bp] != signs[b1] * signs[b2]:
                    found = (b1, b2, bp, signs[b1], signs[b2], signs[bp])
                    break
        if found:
            break
    print("VIOLATION (b1,b2,b1b2, s1,s2,s12):", found)
    # also: is the all-ones / all-(-1) structure? count
    pos = sum(1 for b in reps if signs[b] == 1)
    neg = sum(1 for b in reps if signs[b] == -1)
    print(f"#cosets={len(reps)} pos={pos} neg={neg} zero={len(reps)-pos-neg}")
