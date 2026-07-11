#!/usr/bin/env python3
"""Falsify-first probe for the de Bruijn capstone step (1): the packet-minpoly
hypothesis over K = Q(zeta_{p^a}).

CLAIM (to be formalized): for distinct primes p, q and b >= 1, the minimal
polynomial over K = Q(zeta_{p^a}) of a primitive q^b-th root of unity eta is the
geometric packet  Phi_{q^b}(X) = sum_{t<q} X^(t * q^(b-1)).

Two exact sub-checks (all arithmetic exact, integers / Fractions; no float):

(A) PACKET FORM: Phi_{q^b}(X) computed by exact recursive division equals
    sum_{t<q} X^(t*q^(b-1)).

(B) TOWER RANK (the load-bearing inequality): since minpoly_K(eta) divides
    Phi_{q^b} (deg phi(q^b)), the claim is EQUIVALENT to
    [K(eta):K] >= phi(q^b), which (by the tower formula) is equivalent to
    {xi^u * eta^v : u < phi(p^a), v < phi(q^b)} being Q-linearly independent in
    Q(zeta_n), n = p^a q^b, xi = zeta_n^(q^b), eta = zeta_n^(p^a).
    We verify by exact rank of the phi(n) x phi(n) coordinate matrix
    (coordinates of zeta_n^(u*q^b + v*p^a mod n) reduced mod Phi_n).

NEGATIVE CONTROL: the same construction for NON-coprime (m1, m2) inside
Q(zeta_lcm) must be rank-DEFICIENT (phi(m1)*phi(m2) > phi(lcm) vectors cannot be
independent) — coprimality is load-bearing.

Exit 0 iff every check passes.
"""

from fractions import Fraction
from math import gcd


def poly_trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return poly_trim(r)


def poly_divexact(a, b):
    """Exact division of integer polynomials (b monic-or-+-1-leading), a = b*q."""
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    lead = b[-1]
    assert lead in (1, -1)
    for i in range(len(q) - 1, -1, -1):
        c = a[i + len(b) - 1] // lead
        q[i] = c
        if c:
            for j, y in enumerate(b):
                a[i + j] -= c * y
    assert all(v == 0 for v in a), "non-exact division"
    return poly_trim(q)


def totient(n):
    r, m, d = n, n, 2
    out = n
    fs = set()
    while d * d <= m:
        if m % d == 0:
            fs.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fs.add(m)
    for f in fs:
        out = out // f * (f - 1)
    return out


CYCLO = {}


def cyclotomic(n):
    if n in CYCLO:
        return CYCLO[n]
    # x^n - 1
    num = [0] * (n + 1)
    num[0], num[n] = -1, 1
    for d in range(1, n):
        if n % d == 0:
            num = poly_divexact(num, cyclotomic(d))
    CYCLO[n] = num
    return num


def reduce_pow(e, phiN, modpoly, cache):
    """coordinates of x^e mod modpoly (monic, deg phiN), as integer list len phiN."""
    if e in cache:
        return cache[e]
    if e < phiN:
        v = [0] * phiN
        v[e] = 1
    else:
        prev = reduce_pow(e - 1, phiN, modpoly, cache)
        # multiply by x: shift, then reduce the top coefficient
        top = prev[-1]
        v = [0] + prev[:-1]
        if top:
            for i in range(phiN):
                v[i] -= top * modpoly[i]
    cache[e] = v
    return v


def rank_exact(rows):
    m = [[Fraction(x) for x in row] for row in rows]
    rank, ncols = 0, len(m[0]) if m else 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(m)):
            if m[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        pv = m[rank][col]
        for r in range(len(m)):
            if r != rank and m[r][col] != 0:
                f = m[r][col] / pv
                m[r] = [a - f * b for a, b in zip(m[r], m[rank])]
        rank += 1
    return rank


def tower_rank(m1, m2):
    """rank of {zeta_N^(u*(N//m1) + v*(N//m2))} for u<phi(m1), v<phi(m2), N=lcm."""
    N = m1 * m2 // gcd(m1, m2)
    phiN = totient(N)
    mod = cyclotomic(N)
    assert len(mod) == phiN + 1 and mod[-1] == 1
    cache = {}
    rows = []
    for u in range(totient(m1)):
        for v in range(totient(m2)):
            e = (u * (N // m1) + v * (N // m2)) % N
            rows.append(reduce_pow(e, phiN, mod, cache))
    return rank_exact(rows), len(rows), phiN


def main():
    failures = 0

    # (A) packet form of Phi_{q^b}
    packet_cases = [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (5, 1), (5, 2), (7, 1), (3, 3)]
    for q, b in packet_cases:
        n = q ** b
        got = cyclotomic(n)
        want = [0] * ((q - 1) * q ** (b - 1) + 1)
        for t in range(q):
            want[t * q ** (b - 1)] = 1
        ok = got == poly_trim(want)
        print(f"[A] Phi_{{{q}^{b}}} packet form: {'PASS' if ok else 'FAIL'}")
        failures += 0 if ok else 1

    # (B) tower rank, coprime prime-power pairs (the claim)
    coprime_cases = [(4, 3), (3, 4), (8, 3), (4, 9), (9, 4), (2, 9), (8, 9), (27, 4), (25, 3), (16, 3)]
    for pa, qb in coprime_cases:
        rk, nv, phiN = tower_rank(pa, qb)
        ok = rk == nv == phiN
        print(f"[B] coprime ({pa},{qb}): rank {rk} / vectors {nv} / phi(n) {phiN}: "
              f"{'PASS (full rank = tower equality = packet minpoly)' if ok else 'FAIL'}")
        failures += 0 if ok else 1

    # (C) negative control: whenever phi(m1)*phi(m2) > phi(lcm) (e.g. shared prime
    # power overlap), the vectors MUST be dependent — the full-rank conclusion of (B)
    # is not free, it is exactly the totient-multiplicativity content of coprimality.
    # (Note (6,4) is intentionally EXCLUDED: phi(6)phi(4)=phi(12)=4 — those two
    # quadratic fields are linearly disjoint despite gcd 2, so no deficiency there;
    # measured rank 4 = phi(12), consistent.)
    bad_cases = [(4, 8), (3, 9), (9, 6), (8, 4), (9, 3)]
    for m1, m2 in bad_cases:
        rk, nv, phiN = tower_rank(m1, m2)
        assert nv > phiN, f"control ({m1},{m2}) not a deficiency case"
        ok = rk == phiN and rk < nv  # spans everything but cannot be independent
        print(f"[C] overlap control ({m1},{m2}): rank {rk} = phi(lcm) {phiN} < vectors {nv}: "
              f"{'PASS (deficient as required)' if ok else 'FAIL'}")
        failures += 0 if ok else 1

    print(f"\nTOTAL: {'ALL PASS' if failures == 0 else f'{failures} FAILURES'}")
    raise SystemExit(0 if failures == 0 else 1)


if __name__ == "__main__":
    import sys
    sys.setrecursionlimit(100000)
    main()
