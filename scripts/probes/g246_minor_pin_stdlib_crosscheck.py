#!/usr/bin/env python3
"""Second independent implementation for the G246 follow-up probe.

Cross-check for `g246_minor_pin_stdlib.py` (Bareiss path). This file
recomputes the two pinned 4x4 minors with a DIFFERENT algorithm — direct
cofactor expansion along the first row (Leibniz, no fraction-free
elimination) — and asserts both published integers reproduce exactly:

  cell (8,1009,126)  rows (0,1,2,4)  det = -285768
  cell (10,2011,201) rows (0,1,2,3)  det = 308582838

The cell construction (setup/incidence/subset profiles/quotient) is shared
conceptually with the primary probe but re-implemented here independently
(non-importing copy) so a bug in one file cannot silently reproduce itself.
Pure stdlib; no sympy, no numpy, no float.

SCOPE: finite-order audit (n=8,10); NOT prize closure.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path


# ---------- independent 4x4 determinant: cofactor (Leibniz) ----------

def det_cofactor(M: list[list[int]]) -> int:
    a, b, c, d = M[0]
    e, f, g, h = M[1]
    i, j, k, l = M[2]
    m, n, o, p = M[3]
    return (
        a * (f * (k * p - l * o) - g * (j * p - l * n) + h * (j * o - k * n))
        - b * (e * (k * p - l * o) - g * (i * p - l * m) + h * (i * o - k * m))
        + c * (e * (j * p - l * n) - f * (i * p - l * m) + h * (i * n - j * m))
        - d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m))
    )


# ---------- field setup (re-implemented, no imports from the other file) ----------

def factor_primes(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fs = factor_primes(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(p)


def build_cell(n: int, p: int) -> tuple[list[list[int]], int]:
    """Return the 4-column augmented matrix [e0^c, N e0^c, N^2 e0^c, R6^c] and m."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    logs = [0] * p
    x = 1
    for j in range(p - 1):
        logs[x] = j
        x = x * g % p
    G = [pow(g, m * j, p) for j in range(n)]
    assert 2 not in set(G)

    N = [[0] * m for _ in range(m)]
    for x in range(1, p):
        y = (2 - x) % p
        if y:
            N[logs[x] % m][logs[y] % m] += 1
    assert N == [list(r) for r in zip(*N)]

    dp = [[0] * p for _ in range(7)]
    dp[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for r in range(min(6, used), 0, -1):
            prev, cur = dp[r - 1], dp[r]
            for t, v in enumerate(prev):
                if v:
                    cur[(t + x) % p] += v

    def quot(profile: list[int]) -> list[int]:
        vals = [profile[pow(g, a, p)] for a in range(m)]
        for a, want in enumerate(vals):
            for j in range(1, (p - 1) // m):
                assert profile[pow(g, a + m * j, p)] == want
        return vals

    R = quot(dp[6])
    one = [1] * m
    e0 = [1] + [0] * (m - 1)
    seed = [m * e0[i] - one[i] for i in range(m)]
    Rc = [m * R[i] - sum(R) for i in range(m)]

    def mat_vec(A, v):
        return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]

    cols = [seed]
    v = seed
    for _ in range(2):
        v = mat_vec(N, v)
        cols.append(v)
    cols.append(Rc)
    aug = [[cols[c][r] for c in range(4)] for r in range(m)]
    return aug, m


def minor(aug: list[list[int]], rows: tuple[int, ...]) -> int:
    return det_cofactor([[aug[r][c] for c in range(4)] for r in rows])


def main() -> int:
    checks = [
        ((8, 1009), (0, 1, 2, 4), -285768, "G246 Lean-pinned certificate"),
        ((10, 2011), (0, 1, 2, 3), 308582838, "G246 follow-up second-cell minor"),
    ]
    out = Path(__file__).parent / "_out_g246_minor_pin_stdlib_crosscheck.txt"
    out.write_text("", encoding="utf-8")

    def log(s: str) -> None:
        print(s, flush=True)
        with out.open("a", encoding="utf-8") as f:
            f.write(s + "\n")

    log("G246 follow-up — cross-check via independent cofactor (Leibniz) path")
    ok = True
    for (n, p), rows, expect, note in checks:
        aug, m = build_cell(n, p)
        det = minor(aug, rows)
        status = "PASS" if det == expect else "FAIL"
        if det != expect:
            ok = False
        log(f"  cell n={n} p={p} m={m} rows={rows} det={det} expected={expect} [{note}] -> {status}")
    log("CROSS-CHECK: " + ("ALL MATCH" if ok else "MISMATCH — investigation needed"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
