#!/usr/bin/env python3
"""
char0_witness_check.py -- exact char-0 verification of the census argmax family (ArkLib#371).

The census (probe_char0_incidence_census.py) found, at every n in {8,16,32,64} and both split
primes, the same top-1 canonical incidence set
    S(n) = {(0,0), (1,1), (2,3), (4, n/2+2), (n/2-1, n-3), (n-2, n-1)}.
Here we verify SYMBOLICALLY over the cyclotomic ring Z[x]/Phi_n(x) (n = 2^k, Phi_n = x^{n/2}+1,
an integral domain since Phi_n is irreducible over Q) that S(n) is realized by an admissible
hyperplane, which proves M(n) >= 6 in characteristic zero (no mod-p reduction involved):

  1. v := generalized cross product of (P(0,0), P(1,1), P(2,3)) over the ring; v != 0 (rank 3);
  2. v . P(i,j) == 0 for all six (i,j) in S(n)        (all six incidences hold over Q(zeta_n));
  3. not (v0 == 0 and v3 == 0) and not (v1 == 0 and v2 == 0)      (non-normalizer in char 0);
  4. det = v0*v3 - v1*v2 != 0 in the ring                          (invertible in char 0);
  5. exact incidence count of v over ALL (i,j) in (Z/n)^2 equals 6 (the char-0 count of this
     witness plane is exactly 6 -- no hidden extra incidences).

Exact integer arithmetic; negacyclic convolution for multiplication mod x^{n/2}+1.
"""

import sys


def make_ring(n):
    m = n // 2          # Phi_n = x^m + 1 for n a power of two

    def mono(e):        # x^e mod (x^m + 1), e taken mod n with sign
        e %= n
        c = [0] * m
        if e < m:
            c[e] = 1
        else:
            c[e - m] = -1
        return c

    def add(a, b):
        return [x + y for x, y in zip(a, b)]

    def sub(a, b):
        return [x - y for x, y in zip(a, b)]

    def mul(a, b):
        out = [0] * m
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        k = i + j
                        if k < m:
                            out[k] += ai * bj
                        else:
                            out[k - m] -= ai * bj
        return out

    zero = [0] * m
    one = mono(0)
    return mono, add, sub, mul, zero, one


def cross_normal_ring(P00, Q, R, sub, mul):
    """v_k = (-1)^k det(3x3 minor dropping column k), first row all ones."""
    def D(i, j, k):
        return sub(mul(sub(Q[j], Q[i]), sub(R[k], R[i])),
                   mul(sub(Q[k], Q[i]), sub(R[j], R[i])))
    v0 = D(1, 2, 3)
    v1 = [-c for c in D(0, 2, 3)]
    v2 = D(0, 1, 3)
    v3 = [-c for c in D(0, 1, 2)]
    return v0, v1, v2, v3


def check(n):
    mono, add, sub, mul, zero, one = make_ring(n)

    def point(i, j):
        return (mono(i + j), mono(j), mono(i), one)

    def dot(v, P):
        s = zero
        for vk, pk in zip(v, P):
            s = add(s, mul(vk, pk))
        return s

    S = [(0, 0), (1, 1), (2, 3), (4, n // 2 + 2), (n // 2 - 1, n - 3), (n - 2, n - 1)]
    v = cross_normal_ring(point(0, 0), point(1, 1), point(2, 3), sub, mul)
    v0, v1, v2, v3 = v
    assert any(c != 0 for vk in v for c in vk), "cross product vanished (triple not rank 3)"
    for (i, j) in S:
        assert dot(v, point(i, j)) == zero, f"n={n}: incidence ({i},{j}) FAILS over Z[x]/Phi_n"
    assert not (v0 == zero and v3 == zero), f"n={n}: witness is scaling-normalizer type"
    assert not (v1 == zero and v2 == zero), f"n={n}: witness is inversion-normalizer type"
    det = sub(mul(v0, v3), mul(v1, v2))
    assert det != zero, f"n={n}: witness matrix is singular over Q(zeta_n)"
    cnt = sum(1 for i in range(n) for j in range(n) if dot(v, point(i, j)) == zero)
    assert cnt == 6, f"n={n}: char-0 incidence count of witness is {cnt}, expected 6"
    print(f"n={n}: S(n)={S} realized over Z[x]/(x^{n//2}+1); rank-3 witness, "
          f"non-normalizer, det != 0, exact char-0 count = 6  =>  M({n}) >= 6 PROVEN")


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [8, 16, 32, 64]
    for n in ns:
        check(n)
    print("all witness checks passed.")
