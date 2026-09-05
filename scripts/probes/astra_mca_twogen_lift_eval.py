#!/usr/bin/env python3
"""Compact evaluation of the recursive two-generator deletion construction.

Exact finite arithmetic in the production field. Small checks build actual
polynomials independently; the production cell builds no degree-n arrays and
does not assert that all n+2 projective directions are distinct.
"""

import json
from pathlib import Path
import re

from astra_mca_paircover_four_cosets import label
from astra_mca_two_generator_probe import P, multiply, vanishing, evaluate, projective
from astra_mca_two_generator_delete_probe import divide_linear, linear_combination

G = 303645430271030343624574566109998498685964493478
PRODUCTION_N = 2**30


def quotient(a, b):
    assert b % P
    return a * pow(b % P, -1, P) % P


def same_direction(a, b):
    assert a != (0, 0) and b != (0, 0)
    return (a[0]*b[1]-a[1]*b[0]) % P == 0


class RecursiveMap:
    """Old lambda/kappa residual map and its deletion at exponents 0 and 1."""

    def __init__(self, n):
        assert n >= 16 and n <= PRODUCTION_N and PRODUCTION_N % n == 0
        r, power = 0, 1
        while power < n:
            power *= 4
            r += 1
        assert power == n
        self.n, self.m, self.r = n, n//4, r
        self.omega = pow(G, PRODUCTION_N//n, P)
        assert pow(self.omega, n, P) == 1
        assert pow(self.omega, n//2, P) == P-1
        self.i = pow(self.omega, self.m, P)
        assert self.i*self.i % P == P-1
        self.xi, self.eta = 1, self.omega
        self.anchor_x, self.derivative_x = self.regular_part(self.xi)
        self.anchor_y, self.derivative_y = self.regular_part(self.eta)
        assert self.anchor_x != self.anchor_y
        # At the deleted points the surviving row ratio has one extra term.
        self.row_derivative_x = (self.derivative_x+quotient(self.m, 4*self.xi)) % P
        self.row_derivative_y = (self.derivative_y+quotient(self.m, 4*self.eta)) % P

    def regular_part(self, x):
        """Return H/(X^m+i) and its X derivative at a nonzero point off that fibre."""
        assert x % P
        assert pow(x, self.m, P) != -self.i % P
        z, degree = self.omega*x % P, 1
        total, derivative = 0, 0
        half = quotient(1, 2)
        for _ in range(self.r-1):
            inverse_a = quotient(1, z-self.i)
            inverse_b = quotient(1, z+1)
            total += degree*z*(inverse_a+half*inverse_b)
            derivative += degree*degree*z*(-self.i*inverse_a*inverse_a
                                            + half*inverse_b*inverse_b)
            total %= P
            derivative %= P
            z, degree = pow(z, 4, P), degree*4
        value = -quotient(total-quotient(self.m-1, 2), self.m) % P
        slope = -quotient(derivative, self.m*x) % P
        return value, slope

    def old_direction(self, exponent):
        assert 0 <= exponent < self.n
        x = pow(self.omega, exponent, P)
        if exponent % 4 == 3:
            return 1, 0
        value = self.regular_part(x)[0]
        if exponent % 4 == 2:
            value = (value+quotient(self.i, 2)) % P
        return value, 1

    def ordinary_direction(self, exponent):
        """Exactly one absent-core slot, outside the two deleted coordinates."""
        assert 2 <= exponent < self.n
        x = pow(self.omega, exponent, P)
        numerator, denominator = self.old_direction(exponent)
        first = (numerator-self.anchor_y*denominator)*(x-self.xi) % P
        second = (numerator-self.anchor_x*denominator)*(x-self.eta) % P
        assert first or second
        return first, second

    def private_directions(self):
        """(core,index,row) for both absent cores at each deleted coordinate."""
        gap = (self.anchor_x-self.anchor_y) % P
        return [
            (1, 0, (0, 1)),
            (2, 0, (gap, (self.xi-self.eta)*self.row_derivative_x % P)),
            (1, 1, ((self.xi-self.eta)*self.row_derivative_y % P, gap)),
            (2, 1, (1, 0)),
        ]

    def fourth_fibre_contains(self, direction):
        """Membership in {(x-xi:x-eta): x^m=-i}, via its inverse Mobius map."""
        first, second = direction
        if first == second:
            return False  # The preimage is infinity.
        x = quotient(first*self.eta-second*self.xi, first-second)
        return pow(x, self.m, P) == -self.i % P


def interpolate_h(model, nodes):
    """Independent dense Lagrange interpolation on the fourth fibre."""
    roots = [nodes[e] for e in range(model.n) if e % 4 == 3]
    whole = vanishing(roots)
    assert whole == [model.i]+[0]*(model.m-1)+[1]
    h = [0]*model.m
    for e in range(3, model.n, 4):
        value = (model.i, quotient(model.i, 2), 0)[label(e, model.n)]
        if not value:
            continue
        root = nodes[e]
        term = divide_linear(whole, root)
        scale = quotient(value, model.m*pow(root, model.m-1, P))
        h = linear_combination(h, term, 1, scale)
    return h


def small_check(n):
    model = RecursiveMap(n)
    nodes = [pow(model.omega, e, P) for e in range(n)]
    h = interpolate_h(model, nodes)
    alpha, beta, gamma, delta = 1, model.i, P-1, -model.i % P
    e_a, e_b = (beta-gamma) % P, (gamma-alpha) % P
    q = [-delta % P]+[0]*(model.m-1)+[1]
    p0 = [quotient(-beta, alpha-beta)]+[0]*(model.m-1)+[quotient(1, alpha-beta)]
    q0 = [quotient(alpha, alpha-beta)]+[0]*(model.m-1)+[quotient(-1, alpha-beta)]
    factor_a = [-alpha % P]+[0]*(model.m-1)+[1]
    factor_b = [-beta % P]+[0]*(model.m-1)+[1]
    lam = [[0], multiply(factor_a, linear_combination(p0,h,1,e_a)),
           [(-x) % P for x in multiply(factor_b,linear_combination(q0,h,1,e_b))]]
    kap = [[0], [e_a*x % P for x in multiply(factor_a,q)],
           [-e_b*x % P for x in multiply(factor_b,q)]]
    assert all(len(f) <= n//2+1 for triple in (lam,kap) for f in triple)
    polynomial_checks = 0
    for e, x in enumerate(nodes):
        old_f, old_g = [evaluate(f,x) for f in lam], [evaluate(f,x) for f in kap]
        region = label(e,n)
        a,b = ((0,1),(0,2),(1,2))[region]
        assert old_f[a] == old_f[b] and old_g[a] == old_g[b]
        odd = ({0,1,2}-{a,b}).pop()
        row = (old_f[odd]-old_f[a]) % P,(old_g[odd]-old_g[a]) % P
        assert same_direction(row,model.old_direction(e))
        if e % 4 != 3:
            actual = quotient(evaluate(h,x),evaluate(q,x))
            assert actual == model.regular_part(x)[0]
            dh = [(j*h[j]) % P for j in range(1,len(h))]
            dq = [(j*q[j]) % P for j in range(1,len(q))]
            slope = quotient(evaluate(dh,x)*evaluate(q,x)-evaluate(h,x)*evaluate(dq,x),
                             evaluate(q,x)**2)
            assert slope == model.regular_part(x)[1]
        polynomial_checks += 1
    first = [[0]]+[divide_linear(linear_combination(a,b,1,-model.anchor_y),model.eta)
                  for a,b in zip(lam[1:],kap[1:])]
    second = [[0]]+[divide_linear(linear_combination(a,b,1,-model.anchor_x),model.xi)
                   for a,b in zip(lam[1:],kap[1:])]
    assert all(len(f) <= n//2 for triple in (first,second) for f in triple)
    regions = [[e for e in range(n) if label(e,n)==j] for j in range(3)]
    ab,ac,bc = [e for e in regions[0] if e!=0],[e for e in regions[1] if e!=1],regions[2]
    cores = [sorted(ab+ac+[0,1]),sorted(ab+bc),sorted(ac+bc)]
    assert all(len(core)==(2*n+1)//3-1 for core in cores)
    private = {(j,e):row for j,e,row in model.private_directions()}
    directions = []
    normal_pairs = []
    for e,x in enumerate(nodes):
        fv,gv = [evaluate(f,x) for f in first],[evaluate(f,x) for f in second]
        owner = next(j for j in range(3) if e in cores[j])
        for j in range(3):
            if e in cores[j]:
                assert fv[j]==fv[owner] and gv[j]==gv[owner]
            else:
                row = (fv[owner]-fv[j]) % P,(gv[owner]-gv[j]) % P
                expected = private[j,e] if e in (0,1) else model.ordinary_direction(e)
                assert same_direction(row,expected)
                directions.append(projective(*row))
                if e not in (0,1):
                    normal_pairs.append((e,expected))
    assert len(directions)==n+2 and len(set(directions))==n+2
    # A bounded symbolic-recognition check, not an exponent/field search:
    # reject or identify equivalence to each odd monomial on the n-2 ordinary slots.
    monomial_fits = []
    for exponent in range(1,n,2):
        # Equality of all cross-ratios is necessary and sufficient for one Mobius fit.
        base = normal_pairs[:3]
        u = [pow(nodes[e],exponent,P) for e,_ in base]
        d = [row for _,row in base]
        def wedge(a,b):
            return (a[0]*b[1]-a[1]*b[0]) % P
        fits = True
        for e,row in normal_pairs[3:]:
            z = pow(nodes[e],exponent,P)
            lhs = wedge(row,d[0])*wedge(d[1],d[2])*(z-u[2])*(u[1]-u[0])
            rhs = wedge(row,d[2])*wedge(d[1],d[0])*(z-u[0])*(u[1]-u[2])
            if (lhs-rhs) % P:
                fits = False
                break
        if fits:
            monomial_fits.append(exponent)
    assert not monomial_fits
    return {"n":n,"dense_old_node_checks":polynomial_checks,
            "dense_deleted_slot_checks":len(directions),
            "distinct_deleted_directions":len(set(directions)),
            "odd_monomial_mobius_fits_on_ordinary_slots":monomial_fits}


def production_check():
    model = RecursiveMap(PRODUCTION_N)
    private = model.private_directions()
    assert all(not model.fourth_fibre_contains(row) for _,_,row in private)
    assert len({projective(*row) for _,_,row in private}) == 4
    rotation = 1
    pole = quotient(model.eta+rotation*model.xi, 1+rotation)
    assert pow(pole,model.m,P) != -model.i % P
    assert all((row[1]+rotation*row[0]) % P for _,_,row in private)
    result = {"n":model.n,"m":model.m,"rational_sum_terms":model.r-1,
              "primitive_root":model.omega,"deleted_exponents":[0,1],
              "anchor_x":model.anchor_x,"anchor_y":model.anchor_y,
              "row_derivative_x":model.row_derivative_x,
              "row_derivative_y":model.row_derivative_y,
              "private_directions":[[j,e,list(projective(*row))] for j,e,row in private],
              "private_directions_distinct":4,
              "private_directions_in_fourth_fibre_image":0,
              "selected_slots_finite_after_g_plus_t_f":rotation,
              "fourth_fibre_distinct_by_mobius_injectivity":model.m,
              "guaranteed_distinct_directions":model.m+4,
              "required_to_exceed_budget":model.n+1,
              "remaining_quarter_collision_claim":"UNPROVED_NOT_ENUMERATED"}
    return result


def main():
    root = Path(__file__).resolve().parents[2]
    source = root / 'ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean'
    text = source.read_text()
    assert int(re.search(r'abbrev P : ℕ :=\s*(\d+)',text)[1]) == P
    assert int(re.search(r'abbrev g : ZMod P :=\s*(\d+)',text)[1]) == G
    assert P == PRODUCTION_N*(2**128+192)+1
    for n in (16,64,256):
        print(json.dumps(small_check(n),sort_keys=True),flush=True)
    print(json.dumps(production_check(),sort_keys=True),flush=True)


if __name__ == '__main__':
    main()
