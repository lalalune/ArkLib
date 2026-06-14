#!/usr/bin/env python3
"""Probe (O109 candidate): the Schoenberg/Redei Z-relation theorem.

Claim: for every n, the lattice of Z-relations among the n-th roots of unity
    K_n = { w in Z^n : sum_e w_e zeta^e = 0 }
is exactly the Z-span of the rotated full prime packets
    P_{p,r} = indicator of {r + i*(n/p) : i < p},  p | n prime, r < n/p.

(The N-cone version fails at 3 primes — O105's witness at n = 30 — but the
Z-span version is classical and is the side door into 3+-prime territory.)

Verification per n: (a) every packet lies in K_n (reduce mod Phi_n over Z);
(b) rank(span(packets)) = n - phi(n) = rank(K_n); (c) the packet lattice is
SATURATED in Z^n (all Smith invariant factors = 1).  Since span(P) is then a
saturated sublattice of the saturated lattice K_n with equal rank and
span(P) <= K_n, the two coincide.

Moduli: 12, 36 (two-prime, sanity vs O103), 30, 60, 90 (three-prime incl.
non-squarefree), 105 (odd three-prime), 210 (four-prime).  Exit 0 iff all pass.
"""

import sys
from fractions import Fraction


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def primes_of(n):
    out = []
    m, p = n, 2
    while m > 1:
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
        p += 1 if p == 2 else 2
        if p * p > m and m > 1:
            out.append(m)
            break
    return out


def totient(n):
    out = n
    for p in primes_of(n):
        out = out // p * (p - 1)
    return out


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


def packets(n):
    out = []
    for p in primes_of(n):
        step = n // p
        for r in range(step):
            v = [0] * n
            for i in range(p):
                v[r + i * step] = 1
            out.append(v)
    return out


def rank_rational(rows):
    m = [list(map(Fraction, row)) for row in rows]
    rank, cols = 0, len(m[0]) if m else 0
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
    """Smith normal form invariant factors of an integer matrix (small sizes)."""
    a = [row[:] for row in rows]
    rcount, ccount = len(a), len(a[0])
    invariants = []
    top = 0
    while top < min(rcount, ccount):
        # find smallest nonzero entry in the remaining block
        best = None
        for i in range(top, rcount):
            for j in range(top, ccount):
                if a[i][j] != 0 and (best is None or abs(a[i][j]) < abs(a[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        bi, bj = best
        a[top], a[bi] = a[bi], a[top]
        for row in a:
            row[top], row[bj] = row[bj], row[top]
        # eliminate
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


def main():
    ok = True
    for n in (12, 36, 30, 60, 90, 105, 210):
        phi = cyclotomic(n)
        P = packets(n)
        # (a) packets are relations
        rel_ok = all(all(c == 0 for c in reduce_mod_phi(v[:], phi)) for v in P)
        # (b) rank
        rk = rank_rational(P)
        want = n - totient(n)
        # (c) saturation
        inv = smith_invariants(P)
        sat = all(x == 1 for x in inv)
        good = rel_ok and rk == want and sat
        ok = ok and good
        print(f"n={n}: packets={len(P)} relations_ok={rel_ok} "
              f"rank={rk}/{want} smith_all_one={sat} -> {'PASS' if good else 'FAIL'}")
    print("PROBE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
