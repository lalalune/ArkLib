#!/usr/bin/env python3
"""Adversarial stress test of the corrected two-regime growth law (#389):

    S_max(capped) <= C0 * (n + C(n,t)/q^(m+1))      (k=2, m=1, t=4, cap=6)

over PRIME fields.  Hill-climbs word values per domain point (the full
adversarial space, not just two-branch words), seeded both randomly and from
the two-branch construction, at several n/q regimes.  Reports the achieved
ratio S/(n + mean); the law predicts a bounded constant (probes so far: ~6 at
sub-Johnson tuples, ~1 at the two-branch points).  A diverging ratio refutes;
a stable one calibrates C0.
"""

import random
from itertools import combinations
from collections import defaultdict
from math import comb
import sys

CAP = 6
T = 4


def census(p, D, w):
    """(supply, sum_a, max_a) of the >= T family; supply = Sum C(a,4)."""
    pair_count = defaultdict(int)
    for i, x in enumerate(D):
        for y in D[i + 1:]:
            s = ((w[x] - w[y]) * pow(x - y, -1, p)) % p
            b = (w[x] - s * x) % p
            pair_count[(s, b)] += 1
    supply = sum_a = max_a = 0
    for pc in pair_count.values():
        a = int((1 + (1 + 8 * pc) ** 0.5) / 2 + 1e-9)
        max_a = max(max_a, a)
        if a >= T:
            supply += comb(a, T)
            sum_a += a
    return supply, sum_a, max_a


def two_branch_word(p, D, c):
    half = len(D) // 2
    A = set(D[:half])
    return {x: (x * x + (0 if x in A else c)) % p for x in D}


def hill_climb(p, D, w0, iters, rng):
    """Greedy local search on word values, rejecting cap violations."""
    w = dict(w0)
    best, _, ma = census(p, D, w)
    if ma > CAP:
        return None, None
    for _ in range(iters):
        x = rng.choice(D)
        old = w[x]
        w[x] = rng.randrange(p)
        s, _, ma = census(p, D, w)
        if ma <= CAP and s >= best:
            best = s
        else:
            w[x] = old
    return best, w


def main():
    rng = random.Random(0)
    print("=== adversarial two-regime stress (k=2, m=1): S vs n + C(n,4)/q^2 ===")
    print(f"{'p':>5} {'n':>4} {'seedkind':>10} {'S':>6} {'n+mean':>7} {'ratio':>6}")
    worst = 0.0
    cases = [
        # (p, n) across regimes: n ~ q, n ~ q^0.8, n ~ q^0.67
        (61, 61), (61, 48), (101, 101), (101, 80), (101, 47),
        (151, 120), (151, 60), (251, 120), (251, 63),
    ]
    for (p, n) in cases:
        D = list(range(p)) if n == p else sorted(rng.sample(range(p), n))
        mean = comb(n, 4) / p ** 2
        budget = n + mean
        for kind in ["twobranch", "random"]:
            if kind == "twobranch":
                w0 = two_branch_word(p, D, 1 + rng.randrange(p - 1))
            else:
                w0 = {x: rng.randrange(p) for x in D}
            iters = 300 if n <= 110 else 150
            s, _ = hill_climb(p, D, w0, iters, rng)
            if s is None:
                print(f"{p:>5} {n:>4} {kind:>10}   (seed uncapped, skipped)")
                continue
            ratio = s / budget
            worst = max(worst, ratio)
            print(f"{p:>5} {n:>4} {kind:>10} {s:>6} {budget:>7.0f} {ratio:>6.2f}")
    print(f"\nmax observed S/(n + mean) = {worst:.2f}"
          f"  -> two-regime law {'REFUTED at C0 < ' + str(int(worst) + 1) if worst > 8 else 'consistent (C0 ~ ' + f'{worst:.1f}' + ')'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
