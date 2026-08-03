#!/usr/bin/env python3
"""G246-family extension: degree-2 Krylov countermodel audit at n=16.

Extends the G246/G320/Krylov-degree-2 countermodel family (claimed on #466,
building on PR #524) to subgroup order n=16. Checks whether the rank
obstruction — rank_aug > rank_seed on the 4-column matrix
[e0^c, N e0^c, N^2 e0^c, R6^c] — survives at larger smooth cells
((p-1) % 16 == 0, 2 not in the subgroup G), and pins a nonzero 4-row
minor witness when it does.

Discipline (same as PR #524):
- pure stdlib (no sympy, no numpy, no float in load-bearing values)
- two independent determinant paths (Bareiss + cofactor) cross-check every
  pinned integer
- durable output written as we go
- honest scope: finite-order audit; O(p) enumeration cannot reach
  q ~ n*2^128, so this is NOT prize closure

Result expectation: if rank_seed == rank_aug at n=16, the obstruction dies
at larger order (real negative result — report it). If it holds, the
countermodel family extends one more rung.
"""

from __future__ import annotations

import itertools
import math
import sys
import time
from pathlib import Path

OUT = Path(__file__).parent / "_out_g246_n16_audit.txt"


def log(msg: str) -> None:
    print(msg, flush=True)
    with OUT.open("a", encoding="utf-8") as f:
        f.write(msg + "\n")


# ---------- exact linear algebra: two independent determinant paths ----------

def det_bareiss(M: list[list[int]]) -> int:
    """Fraction-free Bareiss determinant (integer-exact)."""
    n = len(M)
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            swap = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
            if swap is None:
                return 0
            A[k], A[swap] = A[swap], A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * pivot - A[i][k] * A[k][j]) // prev
        prev = pivot
    return sign * A[n - 1][n - 1]


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


def rank_fracfree(A0: list[list[int]], cols: int) -> int:
    A = [row[:] for row in A0]
    rows, r = len(A), 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                gd = math.gcd(A[i][c], A[r][c])
                m1, m2 = A[i][c] // gd, A[r][c] // gd
                for cc in range(c, cols):
                    A[i][cc] = m1 * A[r][cc] - m2 * A[i][cc]
        r += 1
        if r == rows:
            break
    return r


# ---------- field machinery ----------

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
    assert 2 not in set(G), f"n={n} p={p}: 2 in subgroup G (sponsor condition broken)"

    # quotient-incidence N[A,B] = #{x in F_p* : 2-x in F_p*, cls(x)=A, cls(2-x)=B}
    N = [[0] * m for _ in range(m)]
    for x in range(1, p):
        y = (2 - x) % p
        if y:
            N[logs[x] % m][logs[y] % m] += 1
    assert N == [list(row) for row in zip(*N)]

    # subset-sum profiles dp[r][t] = #{S in C(G, r) : sum S = t mod p}, r <= 6
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
    for r in range(7):
        assert sum(dp[r]) == math.comb(n, r)

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

    rank_seed = rank_fracfree(aug[:3], 3)
    rank_aug = rank_fracfree(aug, 4)
    return {
        "n": n, "p": p, "m": m, "G": G,
        "rank_seed": rank_seed, "rank_aug": rank_aug,
        "aug": aug,
        "holds": rank_aug > rank_seed,
    }


def first_nonzero_minor(aug: list[list[int]], cap: int = 2_000_000) -> tuple[int, tuple[int, ...], int] | None:
    """First 4-row subset with nonzero determinant (Bareiss), capped scan."""
    m = len(aug)
    scanned = 0
    for rows in itertools.combinations(range(m), 4):
        scanned += 1
        minor = [[aug[r][c] for c in range(4)] for r in rows]
        d = det_bareiss(minor)
        if d != 0:
            return (d, rows, scanned)
        if scanned >= cap:
            return None
    return None


def main() -> int:
    OUT.unlink(missing_ok=True)
    t0 = time.time()
    log("G246-family extension: degree-2 Krylov countermodel audit at n=16")
    log("builds on PR #524 (n=8, n=10); pure stdlib; two independent det paths")
    log("")

    # smooth n=16 cells: (p-1) % 16 == 0, p prime, 2 not in subgroup G
    cells: list[tuple[int, int]] = []
    p = 257  # 256 % 16 == 0, m = 16
    while len(cells) < 5 and p < 3_000_000:
        if (p - 1) % 16 == 0:
            # quick primality via trial division up to sqrt
            if all(p % d for d in range(2, int(math.isqrt(p)) + 1)):
                # check sponsor condition: 2 not in G (order-16 subgroup)
                g0 = primitive_root(p)
                m0 = (p - 1) // 16
                G0 = {pow(g0, m0 * j, p) for j in range(16)}
                if 2 not in G0:
                    cells.append((16, p))
        p += 16

    results = []
    for n, p in cells:
        r = audit(n, p)
        results.append(r)
        line = (f"n={r['n']} p={p} m={r['m']} rank_seed={r['rank_seed']} "
                f"rank_aug={r['rank_aug']} verdict={'HOLDS' if r['holds'] else 'FLIPS'}")
        log(line)
        if r["holds"]:
            found = first_nonzero_minor(r["aug"])
            if found:
                det, rows, scanned = found
                # cross-check with the independent cofactor path
                minor = [[r["aug"][rr][c] for c in range(4)] for rr in rows]
                det2 = det_cofactor(minor)
                match = "MATCH" if det2 == det else "MISMATCH!"
                log(f"  first nonzero minor: rows={rows} det={det} (after {scanned} subsets; cofactor {match})")
            else:
                log("  no nonzero 4-row minor found in capped scan (cap 2M)")

    flips = [r for r in results if not r["holds"]]
    log("")
    if flips:
        log(f"RESULT: obstruction FLIPPED at n=16 cells {[(r['p']) for r in flips]} -> does not survive larger order")
    else:
        log(f"RESULT: rank obstruction HOLDS at n=16 across {len(results)} cells "
            f"(p in {[r['p'] for r in results]})")
    log(f"wall time: {time.time()-t0:.1f}s")
    log("scope: finite-order audit; NOT prize closure (O(p) enumeration)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
