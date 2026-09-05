#!/usr/bin/env python3
"""Exact controls for a fixed-word differential carrier; no MCA/prize closure."""
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, isqrt
import json

import astra_hasse_order_two_check as local
import astra_mca_single_hole_locator_check as uni


def scalar_counts(D, w, m, cap):
    degree = (D-1)//(w-1)
    coefficients = sum(max(0, D-w*h+j)
                       for h in range(degree+1) for j in range(min(h, cap)+1))
    rank = sum(min(max(0, min(h, r)-max(0, h-cap)+1), m-r)
               for h in range(degree+1) for r in range(m) if r+(w-1)*h < D)
    # Independent summation by R exponent, using arithmetic progressions in i.
    by_r = 0
    for j in range(cap+1):
        width = D-(w-1)*j
        if width <= 0:
            continue
        terms = (width-1)//w+1
        by_r += terms*width-w*terms*(terms-1)//2
    assert coefficients == by_r
    return coefficients, rank, degree


def direct_scalar_rank(D, w, m, cap, prime, node, received):
    """Full substitution in the original monomials; no homogeneous rank formula."""
    degree = (D-1)//(w-1)
    powers = [{(0, 0, 0): 1}]
    terms = {(0, 0, 0): received, (1, 0, 1): 1, (0, 1, 0): 1}
    for _ in range(degree):
        out = {}
        for left, a in powers[-1].items():
            for right, b in terms.items():
                key = tuple(x+y for x, y in zip(left, right))
                if key[0]+2*key[1] < m:
                    out[key] = (out.get(key, 0)+a*b) % prime
        powers.append({key: c for key, c in out.items() if c})
    columns = []
    for j in range(cap+1):
        for i in range(degree+1):
            for a in range(max(0, D-w*i-(w-1)*j)):
                column = {}
                for alpha in range(min(a, m-1)+1):
                    scalar = comb(a, alpha)*pow(node, a-alpha, prime)
                    for (t, z, r), value in powers[i].items():
                        if t+alpha+2*z < m:
                            key = t+alpha, z, r+j
                            column[key] = (column.get(key, 0)+scalar*value) % prime
                columns.append(column)
    return len(columns), local.sparse_rank(columns, prime)


def local_controls():
    cases = 0
    for D, w, m, cap in ((5, 3, 1, 0), (8, 3, 2, 1), (11, 3, 3, 2),
                         (13, 4, 4, 2), (17, 4, 5, 3), (19, 5, 5, 2)):
        count, rank, _ = scalar_counts(D, w, m, cap)
        for prime in (2, 5, 17):
            for node, received in ((0, 0), (2, 3)):
                assert direct_scalar_rank(D, w, m, cap, prime, node, received) == (count, rank)
                cases += 1
    # A finite arithmetic control strictly beyond the Johnson agreement bound.
    c, r, d = scalar_counts(12*16, 11, 12, 4)
    assert (c, r, d) == (7205, 300, 19)
    assert c-24*r == 5 and 16**2 < 24*11
    return {"direct_matrices": cases, "n24_arithmetic_surplus": c-24*r,
            "n24_full_interpolation_kernel_constructed": False}


class Poly:
    """Sparse F17[X,Y,R], used only for exact finite differential controls."""

    def __init__(self, value):
        if isinstance(value, Poly):
            value = value.terms
        if isinstance(value, int):
            value = {(0, 0, 0): value}
        self.terms = {key: c % 17 for key, c in value.items() if c % 17}

    def __add__(self, other):
        terms = dict(self.terms)
        for key, c in Poly(other).terms.items():
            terms[key] = (terms.get(key, 0)+c) % 17
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -c for key, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        terms = {}
        for left, c in self.terms.items():
            for right, d in Poly(other).terms.items():
                key = tuple(a+b for a, b in zip(left, right))
                terms[key] = (terms.get(key, 0)+c*d) % 17
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert exponent >= 0
        result, base = Poly(1), self
        while exponent:
            if exponent & 1:
                result = result*base
            base = base*base
            exponent //= 2
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    def derivative(self, axis):
        terms = {}
        for key, c in self.terms.items():
            if key[axis]:
                out = list(key)
                out[axis] -= 1
                terms[tuple(out)] = c*key[axis]
        return Poly(terms)

    def yr_degree(self):
        return max((y+r for x, y, r in self.terms), default=-1)

    def specialize(self, f, fp):
        # Group by Y,R exponents, then do exact univariate substitution.
        groups = {}
        for (x, y, r), c in self.terms.items():
            coefficients = groups.setdefault((y, r), {})
            coefficients[x] = c
        f_powers, fp_powers = [(1,)], [(1,)]
        for _ in range(max((y for y, r in groups), default=0)):
            f_powers.append(uni.multiply(f_powers[-1], f))
        for _ in range(max((r for y, r in groups), default=0)):
            fp_powers.append(uni.multiply(fp_powers[-1], fp))
        result = (0,)
        for (y, r), coefficients in groups.items():
            row = uni.trim([coefficients.get(i, 0) for i in range(max(coefficients)+1)])
            result = uni.add(result, uni.multiply(row, uni.multiply(f_powers[y], fp_powers[r])))
        return result


def univariate(value):
    return Poly({(i, 0, 0): c for i, c in enumerate(value)})


def derivative(f):
    return uni.trim([i*c for i, c in enumerate(f)][1:])


def upow(f, exponent):
    out = (1,)
    for _ in range(exponent):
        out = uni.multiply(out, f)
    return out


def full_small_list():
    nodes = tuple(x for x in uni.OMEGA if x != 1)
    word = dict.fromkeys(nodes, 0)
    word[2], word[4] = 7, 15
    # Any candidate with five agreements contains a four-node interpolation set.
    candidates = {uni.interpolate(subset, word) for subset in combinations(nodes, 4)}
    decoded = sorted(f for f in candidates if sum(uni.evaluate(f, x) == word[x] for x in nodes) >= 5)
    assert decoded == [(0,), (4, 4, 1, 1), (5, 1, 6, 14)]
    return decoded


def reconstruction_controls():
    fs = full_small_list()
    f1, f2 = fs[1:]
    r1, r2 = derivative(f1), derivative(f2)
    difference = uni.add(f1, uni.scale(-1, f2))
    T = uni.multiply(uni.multiply(f1, f2), difference)
    a1 = uni.add(uni.multiply(r1, r1), r1)
    a2 = uni.add(uni.multiply(r2, r2), r2)
    B = uni.add(uni.scale(-1, uni.multiply(a1, f2)), uni.multiply(a2, f1))
    D = uni.add(uni.scale(-1, uni.multiply(uni.multiply(a1, f2), difference)),
                uni.scale(-1, uni.multiply(B, f1)))
    # F/T=R^2+R+(B/T)Y^2+(D/T)Y is a smooth conic over an algebraic closure
    # of F17(X): its projective determinant is -(B*T+D^2)/(4*T^2).
    assert T != (0,)
    assert uni.add(uni.multiply(B, T), uni.multiply(D, D)) != (0,)
    Y, R = Poly({(0, 1, 0): 1}), Poly({(0, 0, 1): 1})
    F = univariate(T)*(R*R+R)+univariate(B)*Y*Y+univariate(D)*Y
    H = F.derivative(2)
    G = -F.derivative(0)-R*F.derivative(1)
    assert F.yr_degree() == 2 and H.yr_degree() == 1
    for f in fs:
        assert F.specialize(f, derivative(f)) == (0,)
        assert H.specialize(f, derivative(f)) != (0,)

    numerators = {2: G}
    derivative_h_numerator = H*(H.derivative(0)+R*H.derivative(1))+G*H.derivative(2)
    for j in (2, 3):
        N = numerators[j]
        numerators[j+1] = (H*H*(N.derivative(0)+R*N.derivative(1))
                           + H*G*N.derivative(2)-(2*j-3)*N*derivative_h_numerator)
    identities = 0
    for j, N in numerators.items():
        assert N.yr_degree() <= (2*j-3)*(F.yr_degree()-1)+1
        for f in fs:
            actual = f
            for _ in range(j):
                actual = derivative(actual)
            h = H.specialize(f, derivative(f))
            assert N.specialize(f, derivative(f)) == uni.multiply(actual, upow(h, 2*j-3))
            identities += 1
    # Once the specialized derivatives agree, Taylor reconstruction must return
    # constant coefficient values, as an identity in F17[X], not at sampled X.
    for f in fs:
        derivatives = [f]
        for _ in range(3):
            derivatives.append(derivative(derivatives[-1]))
        for j in range(4):
            coefficient = (0,)
            for ell in range(j, 4):
                coefficient = uni.add(coefficient, uni.scale(
                    comb(ell, j)*pow(factorial(ell), -1, 17),
                    uni.multiply((0,)*(ell-j)+((-1)**(ell-j),), derivatives[ell])))
            assert coefficient == (f[j] if j < len(f) else 0,)

    # Separate cases that cannot be silently included in the regular map.
    independent = Poly(1)
    for f in fs:
        independent = independent*(Y-univariate(f))
    assert independent.derivative(2) == 0 and independent.yr_degree() == 3
    assert all(independent.specialize(f, derivative(f)) == (0,) for f in fs)
    singular_example = R*R-4*Y
    assert singular_example.specialize((0,), (0,)) == (0,)
    assert singular_example.derivative(2).specialize((0,), (0,)) == (0,)
    assert singular_example.derivative(1) != 0  # The curve itself is smooth here.

    # In characteristic 5, f=X^5 solves R=0 but first-order Taylor data cannot
    # recover f(U); 5! is not invertible. This is a hypothesis control.
    bad_f = [0]*5+[1]
    bad_derivative = [i*c % 5 for i, c in enumerate(bad_f)][1:]
    assert not any(bad_derivative) and factorial(5) % 5 == 0
    initial_value = sum(c*pow(1, i, 5) for i, c in enumerate(bad_f)) % 5
    actual_at_two = sum(c*pow(2, i, 5) for i, c in enumerate(bad_f)) % 5
    # Every derivative of positive order is zero, so the invertible part of
    # Taylor's formula would give just initial_value at U=2.
    assert actual_at_two != initial_value
    return {"complete_F17_list_size": len(fs), "regular_conic_points": len(fs),
            "cleared_derivative_identities": identities, "Taylor_coefficient_identities": 12,
            "independent_R_case_checked": True, "singular_projection_case_checked": True,
            "characteristic_hypothesis_control": "X^5 solves R=0 in characteristic 5; reconstruction fails"}


def production():
    n, w, a, m, cap, p = 262144, 131071, 181353, 99, 30, 2130706433
    D = m*a
    c, r, d = scalar_counts(D, w, m, cap)
    assert (c, r, d) == (30638265433, 116870, 136)
    assert c-n*r == 1496153
    # Removing one layer of Z exponents from the existing MCA API recovers the
    # scalar coefficient and contact spaces when its total cap covers every h.
    assert local.coefficients(D, w, d+1, cap, 0)-local.coefficients(D, w, d, cap, 0) == c
    assert local.rank_one(D, w, d+1, m, cap)-local.rank_one(D, w, d, m, cap) == r
    calibration_c, calibration_r, _ = scalar_counts(166*a, w, 166, 51)
    assert calibration_c-n*calibration_r == 359640658
    assert p > max(w, d) and all(p % t for t in range(2, isqrt(p)+1))
    numerator_degree = (2*w-3)*(d-1)+1
    carrier_degree = d*numerator_degree
    singular = d*(d-1)
    ratio = Fraction(n-w, a-w)
    bound = (carrier_degree*ratio+singular).__floor__()
    q = p**6
    budget = q//2**128
    pairs = bound*(bound+1)//2
    assert (numerator_degree, carrier_degree, singular) == (35388766, 4812872176, 18360)
    assert bound == 12546010856 < budget == 274980728111395087
    assert pairs == 78701194205707931796 < q
    assert bound*2**128 < q
    return {"n": n, "w": w, "agreements": a, "m": m, "R_cap": cap,
            "weight_cap": D, "YR_degree_cap": d, "coefficients": c,
            "single_node_rank": r, "nullity_lower_bound": c-n*r,
            "carrier_degree_bound": carrier_degree, "singular_allowance": singular,
            "incidence_ratio": str(ratio), "written_uniform_list_bound": bound,
            "field_size": q, "list_budget": budget, "projection_pair_count": pairs,
            "arity": "every positive integer", "MCA_bound_proved": False,
            "production_interpolation_kernel_constructed": False}


def main():
    print(json.dumps({"status": "PASS_SCALAR_DIFFERENTIAL_CARRIER_CONTROLS",
                      "local_rank": local_controls(),
                      "reconstruction": reconstruction_controls(),
                      "production_arithmetic": production(),
                      "independent_mathematical_review": False,
                      "Lean_formalization": False, "prize_solved": False}, indent=2))


if __name__ == "__main__":
    main()
