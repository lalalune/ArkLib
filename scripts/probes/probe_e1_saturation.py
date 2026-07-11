#!/usr/bin/env python3
"""
probe_e1_saturation.py — is E1's bound |N(alpha)| <= (sum c^2)^{m/4} saturable on the
ACTUAL admissible difference set? (Companion to EffectivePerPrimeExactness.md section 5.)

At m = 128 (rho = 1/2, layer r = 65) the eta = 1/128 per-prime window would need an
effective collision threshold below the breach ceiling 2^228.4 — i.e. ~2^27 below
T(128,65) ~ 2^255.3. This probe shows that is impossible for ANY norm-SIZE argument:

  PART 1: hill-climb log2|N(c)| over difference vectors c in {0,±2}^64 with support
          >= 62. Finds c with support 62, sum c^2 = 248, and
          log2|N(c)| = 252.379  vs  E1's (m/4)*log2(248) = 254.534   (gap 2.15 bits).
  PART 2: EXACT verification — |N(c)| computed as an exact integer (determinant of the
          multiplication-by-c matrix on Z[x]/(x^64+1), fraction-free Bareiss), and the
          realization c = eps - eps' with BOTH patterns admissible at layer 65
          (eps = c/2 plus a shared padding coordinate eps[j0] = eps'[j0] = 1 on a free
          slot: supports 63, odd, <= min(65, 63)).

Conclusion: max |N| over the genuine layer-65 difference set is >= 2^252.38 >> 2^228.4,
so the eta=1/128 rho=1/2 window CANNOT be opened by sharpening the norm inequality
(moments, Hoelder, difference-set restriction, ...). Any opening must show p does not
divide N(alpha) arithmetically (splitting structure of the specific prime), or use a
different bad-scalar construction. Deterministic (seed 34). Exit 0 iff all checks pass.
"""
import math
import sys

import numpy as np

m, half, r = 128, 64, 65
odd = np.arange(1, m, 2)
zeta = np.exp(2j * np.pi / m)
Z = zeta ** np.outer(odd, np.arange(half))


def logN(c):
    return float(np.sum(np.log2(np.abs(Z @ c))))


def bound(c):
    return (m / 4) * np.log2(float(np.dot(c, c)))


def hill_climb(seed=34, restarts=24):
    rng = np.random.default_rng(seed)
    best_gap, best = None, None
    for _ in range(restarts):
        eps = rng.choice([-1.0, 1.0], size=half)
        eps[rng.integers(half)] = 0.0
        c = 2 * eps
        cur = logN(c) - bound(c)
        improved = True
        while improved:
            improved = False
            for j in range(half):
                old = c[j]
                for val in (-2.0, 0.0, 2.0):
                    if val == old:
                        continue
                    c[j] = val
                    if np.count_nonzero(c) < 62:
                        c[j] = old
                        continue
                    g = logN(c) - bound(c)
                    if g > cur + 1e-9:
                        cur, improved, old = g, True, c[j]
                    else:
                        c[j] = old
        if best_gap is None or cur > best_gap:
            best_gap, best = cur, c.copy()
    return best_gap, best.astype(int)


def exact_abs_norm(c):
    """|N_{Q(zeta_128)/Q}(sum c_j zeta^j)| as an exact integer:
    |det| of multiplication-by-A on Z[x]/(x^64 + 1) via fraction-free Bareiss."""
    n = half
    M = [[0] * n for _ in range(n)]
    for j, cj in enumerate(int(v) for v in c):
        if cj == 0:
            continue
        for k in range(n):
            idx, sgn = j + k, 1
            while idx >= n:
                idx -= n
                sgn = -sgn  # x^64 = -1
            M[idx][k] += sgn * cj
    prev, sign = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for s in range(k + 1, n):
                if M[s][k] != 0:
                    M[k], M[s] = M[s], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return abs(sign * M[n - 1][n - 1])


if __name__ == "__main__":
    ok = True
    gap, c = hill_climb()
    s2 = int(c @ c)
    print(f"PART 1: best c — support {np.count_nonzero(c)}, sum c^2 = {s2}, "
          f"float log2|N| = {logN(c):.3f}, E1 bound = {bound(c):.3f}, gap = {gap:.3f}")

    N = exact_abs_norm(c)
    l2N = math.log2(N)
    print(f"PART 2a: exact |N(c)| log2 = {l2N:.3f} (integer, {N.bit_length()} bits); "
          f"float agreement: {abs(l2N - logN(c)) < 0.01}")
    ok &= abs(l2N - logN(c)) < 0.01
    ok &= l2N > 252.0  # the headline: far above the 228.4 ceiling

    free = [j for j in range(half) if c[j] == 0]
    j0 = free[0]
    eps = (c // 2).astype(int)
    eps[j0] = 1
    epsp = (-(c // 2)).astype(int)
    epsp[j0] = 1
    smax = min(r, m - r)
    for name, e in (("eps", eps), ("eps'", epsp)):
        s = int(np.count_nonzero(e))
        adm = (s % 2 == r % 2) and (s <= smax) and set(np.unique(e)) <= {-1, 0, 1}
        print(f"PART 2b: {name}: support {s}, admissible at layer {r}: {adm}")
        ok &= adm
    ok &= bool(np.all(eps - epsp == c))
    print(f"PART 2b: eps - eps' == c: {bool(np.all(eps - epsp == c))}")
    print("ALL PASS" if ok else "FAILURE")
    sys.exit(0 if ok else 1)
