#!/usr/bin/env python3
"""Exact higher-product controls; see docs/kb/astra_mca_higher_product_lifts-2026-09-06.md."""
import json

P = 365375409332725729550921208179070755120141565953
PRODUCTION_N = 1 << 30


class Poly:
    """Sparse polynomials with nonnegative exponents over a prime field."""
    def __init__(self, p):
        self.p = p

    def clean(self, a):
        return {i: x % self.p for i, x in a.items() if x % self.p}

    def add(self, a, b):
        out = dict(a)
        for i, x in b.items():
            out[i] = (out.get(i, 0) + x) % self.p
        return self.clean(out)

    def neg(self, a):
        return self.clean({i: -x for i, x in a.items()})

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def scale(self, a, s):
        return self.clean({i: x * s for i, x in a.items()})

    def shift(self, a, j):
        assert all(i + j >= 0 for i in a)
        return {i + j: x for i, x in a.items()}

    def mul(self, a, b):
        out = {}
        for i, x in a.items():
            for j, y in b.items():
                out[i + j] = (out.get(i + j, 0) + x * y) % self.p
        return self.clean(out)

    def power(self, a, q):
        out = {0: 1}
        while q:
            if q & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            q //= 2
        return out

    def cyclic(self, a, n):
        out = {}
        for i, x in a.items():
            out[i % n] = (out.get(i % n, 0) + x) % self.p
        return self.clean(out)

    def eval(self, a, x):
        return sum(c * pow(x, i, self.p) for i, c in a.items()) % self.p

    def degree(self, a):
        return max(a, default=-1)

    def interpolate_subgroup(self, values, omega):
        n = len(omega)
        ni = pow(n, -1, self.p)
        # Direct inverse Fourier transform, independent of polynomial reduction.
        return self.clean({j: ni * sum(v * pow(x, (-j) % n, self.p)
                                    for x, v in zip(omega, values))
                           for j in range(n)})


def subgroup(p, n):
    assert (p - 1) % n == 0 and n & (n - 1) == 0
    for a in range(2, 1000):
        g = pow(a, (p - 1) // n, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) != 1:
            omega = [pow(g, i, p) for i in range(n)]
            assert len(set(omega)) == n
            return omega
    raise AssertionError("No generator found in bounded search")


def example_polynomials(ring, n, c):
    k = n // 2
    t = {k - 2: 1, k + 2: c}
    D = {n - 4: 1, 0: 2 * c, 4: c * c}
    J = ring.shift(ring.power({0: 1, 4: c}, 3), k - 6)
    Q = ring.sub(ring.sub(
        ring.scale(ring.power({0: 2, 4: c}, 3), c ** 3),
        ring.shift({0: 1, 4: 6 * c, 8: 3 * c * c}, n - 12)),
        {2 * n - 12: 1})
    return tuple(ring.clean(a) for a in (t, D, J, Q))


def lift_scalar(ring, D, J, q):
    if q % 2 == 0:
        return ring.power(D, q // 2)
    assert q >= 3
    return ring.mul(J, ring.power(D, (q - 3) // 2))


def dense_control(p, n):
    ring = Poly(p)
    omega = subgroup(p, n)
    k = n // 2
    c = next(c for c in range(2, 100)
             if pow((-pow(c, -1, p)) % p, n // 4, p) != 1)
    t, D, J, Q = example_polynomials(ring, n, c)
    tv = [ring.eval(t, x) for x in omega]
    assert all(tv)
    assert ring.interpolate_subgroup(tv, omega) == t
    assert ring.degree(t) == k + 2 >= k
    assert ring.degree(ring.shift(t, 1)) == k + 3 < n
    assert len({x for x, v in zip(omega, tv) if v}) >= 2
    # Direct row-product interpolation agrees with the quadratic exact lift.
    for j in range(3):
        values = [pow(v, 2, p) * pow(x, j, p) % p
                  for x, v in zip(omega, tv)]
        assert ring.interpolate_subgroup(values, omega) == ring.shift(D, j)
    assert ring.interpolate_subgroup([pow(v, 3, p) for v in tv], omega) == J
    assert ring.mul(D, ring.shift(D, 2)) == ring.power(ring.shift(D, 1), 2)
    lifts = {q: lift_scalar(ring, D, J, q) for q in range(2, 12)}
    tensor_checks = 0
    for q, L in lifts.items():
        for j in range(q + 1):
            coordinate = ring.shift(L, j)
            assert ring.degree(coordinate) <= q * (k - 1)
            values = [pow(v, q, p) * pow(x, j, p) % p
                      for x, v in zip(omega, tv)]
            assert all(ring.eval(coordinate, x) == y
                       for x, y in zip(omega, values))
            # Canonical numerators can wrap; the lift itself obeys the cap.
            assert ring.cyclic(coordinate, n) == ring.interpolate_subgroup(values, omega)
            if j < q:
                assert ring.shift(coordinate, 1) == ring.shift(L, j + 1)
            tensor_checks += 1
        for j in range(q - 1):
            assert ring.mul(ring.shift(L, j), ring.shift(L, j + 2)) == \
                ring.power(ring.shift(L, j + 1), 2)
    for q in range(2, 10):
        assert ring.mul(D, lifts[q]) == lifts[q + 2]
    for even in (2, 4, 6):
        for q in range(2, 12 - even):
            assert ring.mul(lifts[even], lifts[q]) == lifts[even + q]
    defect = ring.sub(ring.power(J, 2), ring.power(D, 3))
    assert defect and ring.degree(defect) == 3 * n - 12
    assert defect == ring.mul({n: 1, 0: p - 1}, Q)
    assert ring.cyclic(defect, n) == {}
    assert ring.power(lifts[3], 2) != lifts[6]
    return {"p": p, "n": n, "c": c, "full_support": True,
            "tensor_coordinate_checks": tensor_checks,
            "orders": [2, 11], "canonical_column_degrees": [k + 2, k + 3],
            "defect_degree": ring.degree(defect), "all_checks": "PASS"}


def true_rs_control():
    p, n = 257, 16
    ring = Poly(p)
    omega = subgroup(p, n)
    k = n // 2
    F, G, H = {0: 1}, {k - 2: 1}, {0: 1, 1: 1}
    D, J = ring.power(H, 2), ring.power(H, 3)
    h0, h1 = ring.mul(H, F), ring.mul(H, G)
    assert max(ring.degree(h0), ring.degree(h1)) == k - 1
    assert ring.power(J, 2) == ring.power(D, 3)
    assert all((ring.eval(h0, x), ring.eval(h1, x)) ==
               (ring.eval(H, x), ring.eval(H, x) * pow(x, k - 2, p) % p)
               for x in omega)
    # A canonical cubic tensor numerator need not have exact rank one for RS.
    C = [ring.cyclic(ring.mul(ring.power(h0, 3 - j), ring.power(h1, j)), n)
         for j in range(4)]
    canonical_defect = ring.sub(ring.mul(C[1], C[3]), ring.power(C[2], 2))
    assert canonical_defect
    # Yet actual unreduced product lifts satisfy every cross-order identity.
    cubic = [ring.mul(ring.power(h0, 3 - j), ring.power(h1, j)) for j in range(4)]
    assert ring.mul(cubic[0], cubic[2]) == ring.power(cubic[1], 2)
    assert max(map(ring.degree, cubic)) <= 3 * (k - 1)
    # Here m=k-2, ell=1, so the positive degree criterion applies.
    assert 6 < n
    # Existential quantifier guard: actual RS can have bad alternate cubic lifts.
    alternate_J = {n: 1}  # 1+V=T^n on mu_n; original E=(1,T), D=1.
    assert ring.degree(alternate_J) <= 3 * (k - 2)
    assert all(ring.eval(alternate_J, x) == 1 for x in omega)
    assert ring.power(alternate_J, 2) != {0: 1}
    return {"p": p, "n": n, "zero_rows": 1,
            "canonical_cubic_rank_one": False,
            "unreduced_cubic_rank_one": True, "cross_order_exact": True,
            "alternate_cubic_of_true_RS_can_fail_cross_order": True}


def zero_row_control():
    p, n = 257, 16
    ring = Poly(p)
    omega = subgroup(p, n)
    k = n // 2
    half = pow(2, -1, p)
    t = {0: half, k: -half % p}
    values = [ring.eval(t, x) for x in omega]
    assert values.count(0) == k and values.count(1) == k
    D, J = t, t
    ell = k - 2
    assert ring.degree(D) <= 2 * ell
    assert 3 * ell >= n - 1
    for q in range(2, 12):
        L = lift_scalar(ring, D, J, q)
        assert ring.degree(L) + q <= q * (k - 1)
        assert all(ring.eval(L, x) == pow(v, q, p) for x, v in zip(omega, values))
    defect = ring.sub(ring.power(J, 2), ring.power(D, 3))
    assert defect and ring.cyclic(defect, n) == {}
    # Repeated-root constraint at zero rows: both defect and its derivative vanish.
    derivative = ring.clean({i - 1: i * a for i, a in defect.items() if i})
    assert all(ring.eval(derivative, x) == 0 for x, v in zip(omega, values) if v == 0)
    return {"p": p, "n": n, "zero_rows": k,
            "all_orders_2_through_11": "PASS", "cross_order_exact": False}


def sparse_production():
    p, n, c = P, PRODUCTION_N, 2
    ring = Poly(p)
    k, M = n // 2, n // 4
    t, D, J, Q = example_polynomials(ring, n, c)
    assert ring.cyclic(ring.power(t, 2), n) == D
    assert ring.cyclic(ring.power(t, 3), n) == J
    defect = ring.sub(ring.power(J, 2), ring.power(D, 3))
    assert defect == ring.mul({n: 1, 0: p - 1}, Q)
    assert ring.degree(defect) == 3 * n - 12
    assert ring.degree(Q) == 2 * n - 12
    nonzero_power = pow(-pow(c, -1, p) % p, M, p)
    assert nonzero_power != 1
    # R(Y)=Y^(M-1)+c^2Y+2c. A common root of R,R' must equal y below.
    assert (M - 1) % p and (M - 2) % p
    y = (-2 * (M - 1) * pow(c * (M - 2), -1, p)) % p
    Ry = (pow(y, M - 1, p) + c * c * y + 2 * c) % p
    assert Ry and 2 * c % p and n % p
    ell = k - 2
    assert ring.degree(D) == 2 * ell
    # D's degree is n-4=2(k-2): its largest tensor coordinate reaches n-2.
    assert ring.degree(J) == k + 6 <= 3 * ell
    for q in range(2, 14):
        L = lift_scalar(ring, D, J, q)
        expected_degree = q * (k - 1) - (n - 12 if q % 2 else 0)
        assert ring.degree(L) + q == expected_degree
        assert ring.cyclic(L, n) == ring.cyclic(ring.power(t, q), n)
    b = 178956971
    assert n == 6 * b - 2 and k == 3 * b - 1
    for m in (1, b - 1, b, 2 * b - 2, 2 * b - 1, k - 1):
        l = k - 1 - m
        assert (3 * l >= n - 1) == (m <= b - 1)
        assert (6 * l < n) == (m >= 2 * b - 1)
    return {"p": p, "n": n, "k": k, "c": c,
            "nonzero_multiplier_power": nonzero_power,
            "R_at_only_possible_repeated_root": Ry,
            "D_squarefree": True, "quadratic_degree": n - 2,
            "cubic_lift_degree": k + 9,
            "defect_degree": ring.degree(defect), "defect_quotient_degree": ring.degree(Q),
            "automatic_m_max": b - 1, "positive_m_min": 2 * b - 1,
            "sparse_orders_checked": [2, 13], "all_checks": "PASS"}


def main():
    receipt = {
        "status": "PASS",
        "dense_controls": [dense_control(p, n) for p in (257, P) for n in (16, 64)],
        "true_rs_control": true_rs_control(),
        "zero_row_control": zero_row_control(),
        "production": sparse_production(),
        "scope": "Higher-product relaxations; no MCA witnesses or universal scalar bound",
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
