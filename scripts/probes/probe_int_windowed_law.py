#!/usr/bin/env python3
"""Probe (O111 candidate): the Z-WINDOWED LAW at every modulus.

Conjecture: for every n, t < n, w : [0,n) -> Z, zeta primitive n-th root (char 0):

    (forall j, 1 <= j <= t -> sum_e w_e zeta^{je} = 0)
      <=>  w in Z-span of { mu_d-coset indicators : d | n, d > t }.

(The N-version is the two-prime O108; at 3+ primes the N-cone fails (O105),
but the Z-lattice version should hold at every n with the Schoenberg level
classification driving the induction.)

Verification per (n, t):
  (a) every d > t coset indicator kills the window (reduce mod Phi_n);
  (b) the coset lattice has rank equal to the Q-kernel dimension of the window
      constraint system (rows = the maps w -> coefficient vector of
      sum_e w_e x^{je} mod Phi_n, for j = 1..t);
  (c) the coset lattice is saturated (Smith invariants all 1).
Together (a)+(b)+(c) prove lattice equality (saturated sublattice of equal rank
inside the kernel lattice, which is itself saturated as a kernel of an integer
matrix... kernel of Z-matrix is saturated by definition).

Moduli: 12, 30 (3-prime), 36, 60 (3-prime non-squarefree), 105; t over several
window lengths. Exit 0 iff all pass.
"""

import sys
from fractions import Fraction


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def cyclotomic(n, cache={}):
    if n in cache:
        return cache[n]
    poly = [-1] + [0] * (n - 1) + [1]
    for d in divisors(n)[:-1]:
        poly = polydiv_exact(poly, cyclotomic(d))
    cache[n] = poly
    return poly


def polydiv_exact(num, den):
    num = num[:]
    dn, dd = len(num) - 1, len(den) - 1
    out = [0] * (dn - dd + 1)
    for k in range(dn - dd, -1, -1):
        c = num[dd + k]
        out[k] = c
        if c:
            for i, dc in enumerate(den):
                num[i + k] -= dc * c
    return out


def reduce_mod_phi(vec, phi):
    poly = vec[:]
    dd = len(phi) - 1
    for k in range(len(poly) - 1, dd - 1, -1):
        c = poly[k]
        if c:
            for i, dc in enumerate(phi):
                poly[i + k - dd] -= dc * c
    return poly[:dd]


def window_matrix(n, t, phi):
    """Rows: for each j in 1..t and each basis exponent e, the contribution of
    w_e to the Phi_n-reduced coefficient vector of sum w_e x^{je}.
    Returns matrix with t*deg rows, n cols."""
    deg = len(phi) - 1
    # residue of x^(je) mod Phi_n, per (j, e)
    rows = [[0] * n for _ in range(t * deg)]
    for j in range(1, t + 1):
        for e in range(n):
            vec = [0] * (j * e + 1)
            vec[j * e] = 1
            if len(vec) < len(phi):
                vec += [0] * (len(phi) - len(vec))
            red = reduce_mod_phi(vec, phi)
            for c in range(deg):
                rows[(j - 1) * deg + c][e] += red[c]
    return rows


def rank_rational(rows):
    m = [list(map(Fraction, row)) for row in rows if any(row)]
    if not m:
        return 0
    rank, cols = 0, len(m[0])
    for c in range(cols):
        piv = next((i for i in range(rank, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        pv = m[rank][c]
        for i in range(len(m)):
            if i != rank and m[i][c] != 0:
                f = m[i][c] / pv
                m[i] = [a - f * b for a, b in zip(m[i], m[rank])]
        rank += 1
    return rank


def smith_invariants(rows):
    a = [row[:] for row in rows]
    rcount, ccount = len(a), len(a[0])
    invariants = []
    top = 0
    while top < min(rcount, ccount):
        best = None
        for i in range(top, rcount):
            for j in range(top, ccount):
                if a[i][j] != 0 and (best is None
                                     or abs(a[i][j]) < abs(a[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        bi, bj = best
        a[top], a[bi] = a[bi], a[top]
        for row in a:
            row[top], row[bj] = row[bj], row[top]
        again = True
        while again:
            again = False
            piv = a[top][top]
            for i in range(top + 1, rcount):
                if a[i][top] % piv != 0:
                    q = a[i][top] // piv
                    a[i] = [x - q * y for x, y in zip(a[i], a[top])]
                    a[top], a[i] = a[i], a[top]
                    again = True
                    piv = a[top][top]
            for i in range(top + 1, rcount):
                q = a[i][top] // piv
                if q:
                    a[i] = [x - q * y for x, y in zip(a[i], a[top])]
            for j in range(top + 1, ccount):
                if a[top][j] % piv != 0:
                    q = a[top][j] // piv
                    for row in a:
                        row[j] -= q * row[top]
                    for row in a:
                        row[top], row[j] = row[j], row[top]
                    again = True
                    piv = a[top][top]
            for j in range(top + 1, ccount):
                q = a[top][j] // piv
                if q:
                    for row in a:
                        row[j] -= q * row[top]
        invariants.append(abs(a[top][top]))
        top += 1
    return invariants


def cosets(n, t):
    out = []
    for d in divisors(n):
        if d > t:
            step = n // d
            for r in range(step):
                v = [0] * n
                for s in range(d):
                    v[r + s * step] = 1
                out.append(v)
    return out


def main():
    ok = True
    cases = [(12, [1, 2, 3, 5]), (30, [1, 2, 4, 5]), (36, [2, 3, 8]),
             (60, [3, 5]), (105, [2, 6])]
    for n, ts in cases:
        phi = cyclotomic(n)
        for t in ts:
            M = window_matrix(n, t, phi)
            kernel_dim = n - rank_rational(M)
            C = cosets(n, t)
            # (a) every coset kills the window
            kills = all(
                all(x == 0 for x in row)
                for v in C
                for row in [[sum(M[i][e] * v[e] for e in range(n))
                             for i in range(len(M))]])
            crank = rank_rational(C)
            inv = smith_invariants(C)
            sat = all(x == 1 for x in inv)
            good = kills and crank == kernel_dim and sat
            ok = ok and good
            print(f"n={n} t={t}: cosets={len(C)} kills={kills} "
                  f"rank={crank}/{kernel_dim} smith_one={sat} "
                  f"-> {'PASS' if good else 'FAIL'}")
    print("PROBE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
