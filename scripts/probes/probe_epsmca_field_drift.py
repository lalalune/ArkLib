#!/usr/bin/env python3
"""Field-drift diagnostic at fixed n = 12, rate 1/2: does the below-Johnson
breakdown recede as the field grows?

probe_epsmca_sampled_rungs.py found total breakdown at delta = 0.25 (below
Johnson 0.293) for RS[F_13, 12, 6] — predicted to be the small-field
degeneracy (poly(n)/|F| = 12/13 is vacuous), not a property of the radius.
This probe tests that prediction by holding (n, k) = (12, 6) and growing the
field: p in {13, 37} (and 61 with --deep).  The two hypotheses separate
cleanly in the data:

  * small-field artifact (predicted): the delta = 0.25 bad-count stays
    roughly constant as p grows, so eps_mca = count/p recedes toward the
    poly(n)/|F| regime;
  * genuinely bad radius (anti-Johnson): the count scales ~ p, breakdown
    persists at every field size.

Sampled lower bounds only (random + monomial worst-line pairs): breakdown
observations are proven, tame observations are provisional.  Witness sets are
trimmed to sizes >= 8 (only thresholds m in {8, 9, 10, 11, 12} are reported;
trimming does not affect those rows).  On success writes
.claude/probe_field_drift_ok for the session gate.  Exit 0 iff asserts pass.
"""

import importlib.util
import os
import random
import sys
from itertools import combinations

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ladder)

random.seed(232)

N, K = 12, 6
MIN_SIZE = 8           # only witness sets of size >= 8 (rows m >= 8 unaffected)
M_ROWS = [12, 11, 10, 9, 8]


class DriftEngine:
    def __init__(self, p):
        self.p = p
        self.xs = ladder.smooth_domain(p, N)
        G = [[pow(x, j, p) for x in self.xs] for j in range(K)]
        self.H = ladder.nullspace(G, p)
        assert len(self.H) == N - K
        self.subsets = []
        for size in range(MIN_SIZE, N + 1):
            self.subsets.extend(combinations(range(N), size))
        self.verif = []
        for S in self.subsets:
            base, rest = S[:K], S[K:]
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
        self.adm = {m: 0 for m in M_ROWS}
        for bit, S in enumerate(self.subsets):
            for m in M_ROWS:
                if len(S) >= m:
                    self.adm[m] |= 1 << bit
        self._cache = {}

    def syndrome(self, w):
        return tuple(sum(h[i] * w[i] for i in range(N)) % self.p for h in self.H)

    def mask(self, syn):
        m = self._cache.get(syn)
        if m is not None:
            return m
        w = ladder.solve_particular(self.H, list(syn), self.p)
        mask = 0
        for bit, tests in enumerate(self.verif):
            ok = True
            for j, base, coeffs in tests:
                if sum(c * w[a] for c, a in zip(coeffs, base)) % self.p != w[j] % self.p:
                    ok = False
                    break
            if ok:
                mask |= 1 << bit
        self._cache[syn] = mask
        return mask

    def profile(self, n_random):
        mono = [self.syndrome([pow(x, e, self.p) for x in self.xs])
                for e in range(N)]
        pairs = [(mono[a], mono[b]) for a in range(N) for b in range(N)]
        d = N - K
        pairs += [(tuple(random.randrange(self.p) for _ in range(d)),
                   tuple(random.randrange(self.p) for _ in range(d)))
                  for _ in range(n_random)]
        best = {m: 0 for m in M_ROWS}
        for s0, s1 in pairs:
            if not any(s1):
                continue
            m0, m1 = self.mask(s0), self.mask(s1)
            pair_ok = m0 & m1
            counts = {m: 0 for m in M_ROWS}
            for g in range(self.p):
                line = tuple((a + g * b) % self.p for a, b in zip(s0, s1))
                bad = self.mask(line) & ~pair_ok
                if bad:
                    for m in M_ROWS:
                        if bad & self.adm[m]:
                            counts[m] += 1
            for m in M_ROWS:
                if counts[m] > best[m]:
                    best[m] = counts[m]
        return best


if __name__ == "__main__":
    deep = "--deep" in sys.argv
    plan = [(13, 120), (37, 45)] + ([(61, 25)] if deep else [])
    results = {}
    for p, n_random in plan:
        eng = DriftEngine(p)
        results[p] = eng.profile(n_random)
        print(f"RS[F_{p}, 12, 6]  (monomial + {n_random} random pairs, "
              f"cache {len(eng._cache)} masks)")
        prev = None
        for m in M_ROWS:
            b = results[p][m]
            print(f"   m={m:>2}  delta={1 - m / N:.3f}  bad gamma >= {b:>3} / {p}")
            if prev is not None:
                assert b >= prev, "monotonicity violated"
            prev = b
        print()
    # the rung's two checks: the p=13 below-Johnson breakdown reproduces, and
    # the drift verdict at delta = 0.25 (m = 9) is computed from the data
    assert results[13][8] >= 12, "expected the p=13 breakdown at delta=1/3"
    c13, c37 = results[13][9], results[37][9]
    ratio_p = 37 / 13
    ratio_c = (c37 / c13) if c13 else float("inf")
    print(f"drift at delta = 0.25 (m = 9): count {c13}/13 -> {c37}/37; "
          f"count ratio {ratio_c:.2f} vs field ratio {ratio_p:.2f}")
    if ratio_c < ratio_p / 2:
        print("verdict: RECEDING — consistent with small-field artifact; "
              "the radius itself is not refuted below Johnson")
    elif ratio_c > 0.8 * ratio_p:
        print("verdict: PERSISTING — bad-count tracks p; delta = 0.25 looks "
              "genuinely bad at n = 12 (anti-Johnson signal, needs deeper look)")
    else:
        print("verdict: AMBIGUOUS — between regimes; extend with --deep (p = 61)")
    stamp = os.path.join(_here, "..", "..", ".claude", "probe_field_drift_ok")
    with open(stamp, "w") as f:
        f.write(f"p13_m9={c13} p37_m9={c37}\n")
    print("\nall assertions passed; stamp written")
