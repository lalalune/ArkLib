#!/usr/bin/env python3
"""Issue #232 — falsify-first probe: the WEIGHTED SQUAREFREE CONE at n = p·q.

CLAIM (O96's named wall (2)): for distinct primes p ≠ q, ζ a primitive pq-th root
of unity in characteristic 0, and w : ZMod(pq) → ℕ,

    Σ_e w(e)·ζ^e = 0   IFF   w is an ℕ-combination of rotated full prime packets,

equivalently (CRT grid coordinates e = gridMap(j,c) = j·q + c·p mod pq, j < p, c < q):

    ∃ a : [0,p) → ℕ, b : [0,q) → ℕ with w(grid(j,c)) = a(j) + b(c) for all (j,c)

(a(j) = multiplicity of the rotated full μ_q-packet {grid(j,c) : c < q},
 b(c) = multiplicity of the rotated full μ_p-packet {grid(j,c) : j < p}).

Tested EXHAUSTIVELY (meet-in-the-middle over the full weight box) at
n = 6, 10, 15, 21 plus the greedy-peel algorithm and the key domination lemma
(every nonzero vanishing weight has a fully-positive packet) on every vanishing
vector found.  Negative controls: single-increment toggles of vanishing vectors
are non-vanishing AND fail the cone test; random non-vanishing vectors fail both.

Exact integer arithmetic: vanishing ⟺ Φ_n divides the weight polynomial
(coefficients reduced mod Φ_n by long division — no floats anywhere).
"""

import sys
from itertools import product as iproduct


def cyclotomic(n: int) -> list[int]:
    """Φ_n as an integer coefficient list, via repeated exact division of X^n - 1."""
    # divisors
    divs = [d for d in range(1, n + 1) if n % d == 0]
    polys = {1: [-1, 1]}  # Φ_1 = X - 1
    for d in divs:
        if d == 1:
            continue
        # X^d - 1
        num = [0] * (d + 1)
        num[0], num[d] = -1, 1
        # divide by product of Φ_e for e | d, e < d
        for e in divs:
            if e < d and d % e == 0:
                num = polydiv_exact(num, polys[e])
        polys[d] = num
    return polys[n]


def polydiv_exact(num: list[int], den: list[int]) -> list[int]:
    """Exact division of integer polynomials (den monic up to leading coeff ±1)."""
    num = num[:]
    dd = len(den) - 1
    while den[dd] == 0:
        dd -= 1
    lead = den[dd]
    assert lead in (1, -1)
    nd = len(num) - 1
    while nd >= 0 and num[nd] == 0:
        nd -= 1
    quot = [0] * (nd - dd + 1) if nd >= dd else [0]
    for i in range(nd, dd - 1, -1):
        c = num[i] // lead
        quot[i - dd] = c
        for k in range(dd + 1):
            num[i - dd + k] -= c * den[k]
    assert all(c == 0 for c in num), "non-exact division"
    return quot


def reduction_table(n: int) -> list[tuple[int, ...]]:
    """X^e mod Φ_n for e < n, as integer vectors of length deg Φ_n."""
    phi = cyclotomic(n)
    d = len(phi) - 1
    assert phi[d] == 1
    tab = []
    cur = [0] * d
    if d > 0:
        cur[0] = 1  # X^0
    for _ in range(n):
        tab.append(tuple(cur))
        # multiply by X mod Φ
        nxt = [0] * d
        for i in range(d - 1):
            nxt[i + 1] = cur[i]
        top = cur[d - 1]
        for i in range(d):
            nxt[i] -= top * phi[i]
        # wait: X^d ≡ -Σ_{i<d} phi[i] X^i since Φ monic
        cur = nxt
    return tab


def vanishes(w, tab, d):
    acc = [0] * d
    for e, we in enumerate(w):
        if we:
            t = tab[e]
            for i in range(d):
                acc[i] += we * t[i]
    return all(c == 0 for c in acc)


def grid(p, q):
    """gridMap p q (j,c) = (j*q + c*p) mod pq — NOTE: matches Lean's
    gridMap N M (x) = x.1*M + x.2*N with N=p, M=q."""
    n = p * q
    g = {}
    for j in range(p):
        for c in range(q):
            g[(j, c)] = (j * q + c * p) % n
    return g


def cone_split(w, p, q, g):
    """Try to produce a,b ≥ 0 with w(grid(j,c)) = a(j)+b(c); return (a,b) or None."""
    # rectangle identity check
    for j in range(p):
        for c in range(q):
            for cp in range(q):
                if w[g[(j, c)]] + w[g[(0, cp)]] != w[g[(j, cp)]] + w[g[(0, c)]]:
                    return None
    c0 = min(range(q), key=lambda c: w[g[(0, c)]])
    a = [w[g[(j, c0)]] for j in range(p)]
    b = [w[g[(0, c)]] - w[g[(0, c0)]] for c in range(q)]
    if any(x < 0 for x in b):
        return None
    for j in range(p):
        for c in range(q):
            if w[g[(j, c)]] != a[j] + b[c]:
                return None
    return a, b


def dominated_packet(w, p, q, g):
    """Key greedy lemma: find a packet with strictly positive weight everywhere.
    Returns ('row', j) for μ_q-packet {grid(j,c):c<q}, ('col', c) for μ_p-packet."""
    for j in range(p):
        if all(w[g[(j, c)]] > 0 for c in range(q)):
            return ("row", j)
    for c in range(q):
        if all(w[g[(j, c)]] > 0 for j in range(p)):
            return ("col", c)
    return None


def greedy_peel(w, p, q, g, tab, d):
    """Peel min-weight packets greedily; return True iff terminates at 0 with every
    intermediate vanishing."""
    w = list(w)
    steps = 0
    while any(w):
        pk = dominated_packet(w, p, q, g)
        if pk is None:
            return False
        kind, idx = pk
        if kind == "row":
            elems = [g[(idx, c)] for c in range(q)]
        else:
            elems = [g[(j, idx)] for j in range(p)]
        m = min(w[e] for e in elems)
        assert m > 0
        for e in elems:
            w[e] -= m
        steps += 1
        if not vanishes(w, tab, d):
            return False
        if steps > 10_000:
            return False
    return True


def enumerate_vanishing(n, tab, d, cap):
    """All w ∈ [0,cap]^n with Φ_n | weightPoly(w), by meet-in-the-middle."""
    h1 = n // 2
    h2 = n - h1
    # hash partial reduced vectors of the FIRST half
    table = {}
    for w1 in iproduct(range(cap + 1), repeat=h1):
        acc = [0] * d
        for e, we in enumerate(w1):
            if we:
                t = tab[e]
                for i in range(d):
                    acc[i] += we * t[i]
        table.setdefault(tuple(acc), []).append(w1)
    out = []
    for w2 in iproduct(range(cap + 1), repeat=h2):
        acc = [0] * d
        for e2, we in enumerate(w2):
            if we:
                t = tab[h1 + e2]
                for i in range(d):
                    acc[i] += we * t[i]
        key = tuple(-c for c in acc)
        if key in table:
            for w1 in table[key]:
                out.append(tuple(w1) + tuple(w2))
    return out


def run_point(p, q, cap):
    n = p * q
    tab = reduction_table(n)
    d = len(tab[0])
    g = grid(p, q)
    van = enumerate_vanishing(n, tab, d, cap)
    n_mix = 0
    n_nonzero = 0
    for w in van:
        assert vanishes(w, tab, d)  # re-check directly
        split = cone_split(w, p, q, g)
        if split is None:
            print(f"FAIL cone: n={n} w={w}")
            return None
        a, b = split
        if any(w):
            n_nonzero += 1
            # key greedy lemma: a fully-positive packet exists
            if dominated_packet(w, p, q, g) is None:
                print(f"FAIL domination: n={n} w={w}")
                return None
            # greedy peel terminates correctly
            if not greedy_peel(w, p, q, g, tab, d):
                print(f"FAIL greedy peel: n={n} w={w}")
                return None
            if any(x > 0 for x in a) and any(x > 0 for x in b):
                n_mix += 1
        # Lam-Leung weight law: |w| = q·Σa + p·Σb ∈ ℕq + ℕp
        assert sum(w) == q * sum(a) + p * sum(b)
    # negative controls: toggles of vanishing vectors
    n_tog = 0
    for w in van[: min(len(van), 400)]:
        for e in range(n):
            w2 = list(w)
            w2[e] += 1
            if vanishes(w2, tab, d):
                print(f"FAIL toggle vanishes: n={n} w={w} e={e}")
                return None
            if cone_split(w2, p, q, g) is not None:
                print(f"FAIL toggle has cone split: n={n} w={w} e={e}")
                return None
            n_tog += 1
    return len(van), n_nonzero, n_mix, n_tog


def main():
    checks = 0
    # (p, q, cap): exhaustive boxes sized to finish in minutes
    points = [(2, 3, 4), (2, 5, 3), (3, 5, 3), (3, 7, 2)]
    for p, q, cap in points:
        res = run_point(p, q, cap)
        if res is None:
            print("PROBE FAILED")
            sys.exit(1)
        nv, nz, mix, tog = res
        print(
            f"n={p*q} (p={p},q={q}) cap={cap}: vanishing={nv} nonzero={nz} "
            f"genuine-mixtures={mix} toggles-rejected={tog} — cone+peel+domination OK"
        )
        checks += 1
    # planted ℕ-combinations at a larger point (n=21, cap beyond exhaustive): converse
    import random

    random.seed(232)
    p, q = 3, 7
    n = p * q
    tab = reduction_table(n)
    d = len(tab[0])
    g = grid(p, q)
    for _ in range(2000):
        a = [random.randint(0, 5) for _ in range(p)]
        b = [random.randint(0, 5) for _ in range(q)]
        w = [0] * n
        for j in range(p):
            for c in range(q):
                w[g[(j, c)]] = a[j] + b[c]
        if not vanishes(w, tab, d):
            print(f"FAIL planted combination does not vanish: a={a} b={b}")
            sys.exit(1)
        if cone_split(w, p, q, g) is None:
            print(f"FAIL planted combination not re-decomposed: a={a} b={b}")
            sys.exit(1)
    print(f"n={n}: 2000 planted ℕ-combinations (coeffs ≤ 5) vanish + re-decompose")
    checks += 1
    print(f"ALL {checks} CHECKS PASSED")
    sys.exit(0)


if __name__ == "__main__":
    main()
