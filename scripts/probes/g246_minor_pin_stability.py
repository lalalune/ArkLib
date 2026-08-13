#!/usr/bin/env python3
"""G246 follow-up — verdict stability at larger prime fields.

Answers the mission's "does the verdict flip?" question: the rank-structure
verdict (rank_aug > rank_seed) and the pinned-minor existence are re-run at
larger primes than the published cells. If the verdict flips at a larger
field, the small-cell result is a "small-q artifact" and must be reported as
such. If it holds, the finite-order countermodel is stable across the tested
range (still NOT prize closure: exhaustive enumeration is O(p) memory, so
q ~ n*2^128 is out of reach for this method).

Cells (all smooth: (p-1) % n == 0, 2 not in subgroup G):
  n=8:  p = 1009 (published), 104729, 1000081?  -> choose certified primes
  n=10: p = 2011 (published), 30011, 1000003?

Prime candidates verified by trial division here (stdlib). Pure stdlib; no
sympy/numpy/float.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path


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


def audit(n: int, p: int) -> dict:
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

    def quot(profile):
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

    # rank via fraction-free elimination
    def rank(A0):
        A = [r[:] for r in A0]
        rows, r = len(A), 0
        for c in range(4):
            pivot = next((i for i in range(r, rows) if A[i][c] != 0), None)
            if pivot is None:
                continue
            A[r], A[pivot] = A[pivot], A[r]
            for i in range(rows):
                if i != r and A[i][c] != 0:
                    gd = math.gcd(A[i][c], A[r][c])
                    m1, m2 = A[i][c] // gd, A[r][c] // gd
                    for cc in range(c, 4):
                        A[i][cc] = m1 * A[r][cc] - m2 * A[i][cc]
            r += 1
            if r == rows:
                break
        return r

    rs = rank(aug[:3])
    ra = rank(aug)
    # nonzero minor at pinned rows?
    pinned = (0, 1, 2, 3)
    minor = [[aug[r][c] for c in range(4)] for r in pinned]
    # 4x4 det via Bareiss
    M = [row[:] for row in minor]
    det = None
    if len(M) == 4 and all(len(r) == 4 for r in M):
        det = 0
        def d4(Mm):
            a, b, c, d = Mm[0]
            e, f, g, h = Mm[1]
            i, j, k, l = Mm[2]
            n, o, p2, q = Mm[3]
            return (
                a * (f * (k * q - l * p2) - g * (j * q - l * o) + h * (j * p2 - k * o))
                - b * (e * (k * q - l * p2) - g * (i * q - l * n) + h * (i * p2 - k * n))
                + c * (e * (j * q - l * o) - f * (i * q - l * n) + h * (i * o - j * n))
                - d * (e * (j * p2 - k * o) - f * (i * p2 - k * n) + g * (i * o - j * n))
            )
        det = d4(M)
    return {"n": n, "p": p, "m": m, "rank_seed": rs, "rank_aug": ra,
            "holds": ra > rs, "det_pinned": det}


def main() -> int:
    out = Path(__file__).parent / "_out_g246_stability.txt"
    out.write_text("", encoding="utf-8")

    def log(s):
        print(s, flush=True)
        with out.open("a", encoding="utf-8") as f:
            f.write(s + "\n")

    log("G246 follow-up — verdict stability across larger primes")
    cells = []
    for n in (8, 10):
        got = 0
        # published cells first, then larger primes with (p-1) % n == 0
        start = 1009 if n == 8 else 2011
        p = start
        while got < 3 and p < 2_000_000:
            if (p - 1) % n == 0 and is_prime(p):
                cells.append((n, p))
                got += 1
            # next candidate with (p-1) % n == 0: step by n
            p += n
            if p <= start:
                break
    seen = set()
    results = []
    for n, p in cells:
        if p in seen:
            continue
        seen.add(p)
        r = audit(n, p)
        results.append(r)
        log(f"  n={r['n']} p={r['p']} m={r['m']} rank_seed={r['rank_seed']} "
            f"rank_aug={r['rank_aug']} verdict={'HOLDS' if r['holds'] else 'FLIPS'} "
            f"det_pinned={r['det_pinned']}")
    flips = [r for r in results if not r["holds"]]
    if flips:
        log("RESULT: verdict FLIPPED at larger primes -> small-q artifact for those cells")
    else:
        log(f"RESULT: verdict STABLE across {len(results)} cells (p up to {max(r['p'] for r in results)})")
        log("note: exhaustive enumeration is O(p) memory; q ~ n*2^128 not reachable by this method")
    log("scope: finite-order stability audit; NOT prize closure")
    return 0


if __name__ == "__main__":
    sys.exit(main())
