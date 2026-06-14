#!/usr/bin/env python3
"""Sampled MCA error profiles at larger block lengths (ladder rungs n = 8, 12).

Extends probe_exact_epsmca_ladder.py past the exact-sup feasibility wall with an
HONEST sampled lower bound: random syndrome pairs plus the deterministic
KKH-style monomial pairs (u0 = x^a, u1 = x^b — the known-worst lines).  Sampling
can only UNDER-report bad scalars, so any observed breakdown is real breakdown;
only "tame" classifications are provisional.

Engine cross-check (two witnesses): the sampling engine, run in full-enumeration
mode on RS[F_7, 6, 3], must reproduce the exact profile computed independently
by probe_exact_epsmca_ladder.eps_profile_syndrome.

The question the rungs answer: on the finer 1/n radius grids, does the
tame->breakdown transition (numerator constant in p vs numerator ~ p) stay at
the Johnson radius 1 - sqrt(rho) as n grows?

Exit 0 iff all assertions pass.
"""

import importlib.util
import os
import random
import sys
from itertools import combinations, product

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ladder)

random.seed(232)  # reproducibility


class Engine:
    """Lazy syndrome-mask MCA engine with precomputed Lagrange verification."""

    def __init__(self, p, n, k):
        self.p, self.n, self.k = p, n, k
        self.xs = ladder.smooth_domain(p, n)
        G = [[pow(x, j, p) for x in self.xs] for j in range(k)]
        self.H = ladder.nullspace(G, p)
        assert len(self.H) == n - k
        self.subsets = []
        for size in range(k + 1, n + 1):
            self.subsets.extend(combinations(range(n), size))
        # Lagrange verification tables: for each subset, for each point beyond
        # the first k, the coefficients expressing the interpolant there.
        self.verif = []
        for S in self.subsets:
            base, rest = S[:k], S[k:]
            tests = []
            for j in rest:
                coeffs = []
                for a in base:
                    num, den = 1, 1
                    for b in base:
                        if b != a:
                            num = num * ((self.xs[j] - self.xs[b]) % p) % p
                            den = den * ((self.xs[a] - self.xs[b]) % p) % p
                    coeffs.append(num * pow(den, p - 2, p) % p)
                tests.append((j, base, coeffs))
            self.verif.append(tests)
        self.adm = {m: ladder.admissible_mask(self.subsets, m)
                    for m in range(k + 1, n + 1)}
        self._mask_cache = {}

    def syndrome(self, w):
        return tuple(sum(h[i] * w[i] for i in range(self.n)) % self.p
                     for h in self.H)

    def mask(self, syn):
        m = self._mask_cache.get(syn)
        if m is not None:
            return m
        w = ladder.solve_particular(self.H, list(syn), self.p)
        mask = 0
        for bit, tests in enumerate(self.verif):
            ok = True
            for j, base, coeffs in tests:
                val = sum(c * w[a] for c, a in zip(coeffs, base)) % self.p
                if val != w[j] % self.p:
                    ok = False
                    break
            if ok:
                mask |= 1 << bit
        self._mask_cache[syn] = mask
        return mask

    def bad_counts(self, s0, s1):
        """Per witness-size threshold m: number of bad gamma for the pair."""
        m0, m1 = self.mask(s0), self.mask(s1)
        pair_ok = m0 & m1
        out = {m: 0 for m in self.adm}
        for g in range(self.p):
            line = tuple((a + g * b) % self.p for a, b in zip(s0, s1))
            bad = self.mask(line) & ~pair_ok
            if bad:
                for m, am in self.adm.items():
                    if bad & am:
                        out[m] += 1
        return out

    def profile(self, pairs):
        best = {m: 0 for m in self.adm}
        for s0, s1 in pairs:
            if not any(s1):
                continue
            for m, c in self.bad_counts(s0, s1).items():
                if c > best[m]:
                    best[m] = c
        return best

    def monomial_pairs(self):
        """Syndromes of all monomial pairs (x^a, x^b), 0 <= a,b < n."""
        syns = [self.syndrome([pow(x, e, self.p) for x in self.xs])
                for e in range(self.n)]
        return [(syns[a], syns[b]) for a in range(self.n) for b in range(self.n)]

    def random_pairs(self, count):
        d = self.n - self.k
        return [(tuple(random.randrange(self.p) for _ in range(d)),
                 tuple(random.randrange(self.p) for _ in range(d)))
                for _ in range(count)]


def show(p, n, k, best, label):
    from math import sqrt
    rho = k / n
    print(f"\nRS[F_{p}, n={n}, k={k}]  rate={rho:.3f}  Johnson={1 - sqrt(rho):.3f}  "
          f"capacity={1 - rho:.3f}   [{label}]")
    print(f"  {'m':>3} {'delta':>7} {'max bad gamma (sampled lower bound)':>36}")
    prev = None
    for m in sorted(best, reverse=True):
        b = best[m]
        marker = "  <-- breakdown" if b >= p - 1 else ""
        print(f"  {m:>3} {1 - m / n:>7.3f} {b:>14} / {p}{marker}")
        if prev is not None:
            assert b >= prev, "monotonicity in delta violated"
        prev = b


if __name__ == "__main__":
    # --- engine cross-check: full enumeration at (7,6,3) must match the exact probe
    eng = Engine(7, 6, 3)
    syns = list(product(range(7), repeat=3))
    full = eng.profile([(a, b) for a in syns for b in syns])
    exact, _ = ladder.eps_profile_syndrome(7, 6, 3)
    assert full == exact, f"engine mismatch: {full} vs {exact}"
    print("engine cross-check: sampling engine (full mode) == exact probe at "
          "RS[F_7,6,3]  [OK]")

    # --- rung n=8, rate 1/2, two fields (drift diagnostic), grid step 1/8
    for p, n, k, nrand in [(17, 8, 4, 40000), (41, 8, 4, 4000)]:
        eng = Engine(p, n, k)
        pairs = eng.monomial_pairs() + eng.random_pairs(nrand)
        best = eng.profile(pairs)
        show(p, n, k, best, f"monomial + {nrand} random pairs")

    # --- rung n=12, rate 1/2, grid step 1/12 (stretch; small sample)
    p, n, k, nrand = 13, 12, 6, 250
    eng = Engine(p, n, k)
    pairs = eng.monomial_pairs() + eng.random_pairs(nrand)
    best = eng.profile(pairs)
    show(p, n, k, best, f"monomial + {nrand} random pairs")

    print("\nReading: breakdown rows (count ~ p) are PROVEN bad radii (sampling")
    print("only under-reports).  Tame rows are provisional upper-regime evidence.")
    print("Compare the first breakdown delta against Johnson per code.")
    print("\nall assertions passed")
