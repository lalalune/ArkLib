#!/usr/bin/env python3
"""Exact rank-incidence identities and decoded controls; no universal rank cap."""
from fractions import Fraction
from itertools import combinations
import json

from astra_mca_locator_pencils_check import evaluate, locator, mul, rank


class Polynomial:
    """Sparse Z[b,L,u], for exact identities without a symbolic dependency."""

    def __init__(self, value):
        if isinstance(value, Polynomial):
            value = value.terms
        if isinstance(value, int):
            value = {(0, 0, 0): value}
        self.terms = {powers: c for powers, c in value.items() if c}

    def __add__(self, other):
        terms = dict(self.terms)
        for powers, c in Polynomial(other).terms.items():
            terms[powers] = terms.get(powers, 0) + c
        return Polynomial(terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({powers: -c for powers, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Polynomial(other)

    def __rsub__(self, other):
        return Polynomial(other) + -self

    def __mul__(self, other):
        terms = {}
        for powers, c in self.terms.items():
            for exponents, d in Polynomial(other).terms.items():
                key = tuple(x + y for x, y in zip(powers, exponents))
                terms[key] = terms.get(key, 0) + c*d
        return Polynomial(terms)

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.terms == Polynomial(other).terms


def exact_identities():
    b = Polynomial({(1, 0, 0): 1})
    cap = Polynomial({(0, 1, 0): 1})
    u = Polynomial({(0, 0, 1): 1})
    count = 4*cap+1
    nodes = 5*b+u
    a = b+1+u
    pair_union = 2*b+2+u

    def n_times_f(s):
        return s*s-(2*count-1)*nodes*s+count*(count-1)*pair_union*nodes

    assert n_times_f(cap*nodes) == nodes*cap*(
        3*(1-cap)*b+32*cap+8+3*(3*cap+1)*u)
    assert n_times_f(count*a) == count*(
        (b+1)*((4*cap-4)*b+4*cap+1)
        - ((12*cap+4)*b-8*cap-1)*u)
    assert (3*(3*cap+1)*(b+1)*((4*cap-4)*b+4*cap+1)
            - (3*(cap-1)*b-32*cap-8)*((12*cap+4)*b-8*cap-1)
            == 5*(4*cap+1)*((24*cap+4)*b-11*cap-1))
    return 3


def endpoint_checks():
    cases = 0
    for b in list(range(3, 51)) + [178956971]:
        for cap in list(range(1, 31)) + [4**14]:
            count = 4*cap+1
            lower = Fraction((b+1)*((4*cap-4)*b+4*cap+1),
                             (12*cap+4)*b-8*cap-1)
            upper = Fraction(3*(cap-1)*b-32*cap-8, 3*(3*cap+1))
            assert lower > upper
            for u in sorted({0, b-3, (b-3)//2}):
                nodes, a, pair_union = 5*b+u, b+1+u, 2*b+2+u
                assert 2*a < nodes
                endpoints = [cap*nodes, count*a]
                vertex = Fraction((2*count-1)*nodes, 2)
                assert max(endpoints) < vertex

                def f(s):
                    return Fraction(s*s, nodes)-(2*count-1)*s+count*(count-1)*pair_union

                assert max(f(endpoint) for endpoint in endpoints) > 0
                assert f(min(endpoints)) > 0
                cases += 1
    return cases


def four_member_fixture():
    """Reconstruct the pencil word, retaining candidates for rank checks."""
    p = 101
    private = [{pow(2, j+20*t, p) for t in range(5)} for j in range(4)]
    shared = pow(2, 4, p)
    assert len(set().union(*private)) == 20
    assert shared not in set().union(*private)
    nodes = sorted(set().union(*private) | {shared})
    us = [locator(errors, p) for errors in private]
    parameters = [-pow(2, 5*j, p) % p for j in range(4)]
    fs = [[0]]
    for i in range(1, 4):
        f = [1]
        for j in range(4):
            if j not in (0, i):
                f = mul(f, us[j], p)
        fs.append([(parameters[0]-parameters[i])*c % p for c in f])
    word = {}
    for i, errors in enumerate(private):
        for x in errors:
            matches = {evaluate(f, x, p) for j, f in enumerate(fs) if j != i}
            assert len(matches) == 1
            word[x] = next(iter(matches))
            assert word[x] != evaluate(fs[i], x, p)
    shared_values = {evaluate(f, shared, p) for f in fs}
    assert len(shared_values) == 4
    word[shared] = next(value for value in range(5) if value not in shared_values)
    assert set(word) == set(nodes)
    return p, nodes, shared, word, fs


def check_family(p, nodes, b, word, fs):
    n, k, agreement, error_bound = 6*b-3, 3*b-1, 4*b-1, 2*b-2
    assert len(nodes) == n and len(set(nodes)) == n
    assert all(len(f)-1 < k for f in fs)
    signatures = {tuple(evaluate(f, x, p) for x in nodes) for f in fs}
    assert len(signatures) == len(fs)
    errors = [{x for x in nodes if evaluate(f, x, p) != word[x]} for f in fs]
    assert all(len(nodes)-len(es) >= agreement for es in errors)
    polys = [locator(es, p) for es in errors]
    rows = [f+[0]*(error_bound+1-len(f)) for f in polys]
    dimension = rank(rows, p)
    assert len(fs) <= 4**(dimension-1)
    for left, right in combinations(errors, 2):
        assert len(left | right) >= n-k+1
    common = set.intersection(*errors)
    maximal_incidence = 0
    for x in set(nodes)-common:
        subset = [row for row, es in zip(rows, errors) if x in es]
        assert any(evaluate(f, x, p) for f in polys)
        if subset:
            subrank = rank(subset, p)
            assert subrank <= dimension-1
            assert len(subset) <= 4**(subrank-1)
        maximal_incidence = max(maximal_incidence, len(subset))
    if len(fs) > 1:
        assert len(common) <= b-3
        assert maximal_incidence >= 1
        assert len(fs) <= 4*maximal_incidence
        sizes = [len(es)-len(common) for es in errors]
        total = sum(sizes)
        nodes_left = n-len(common)
        pair_union = n-k+1-len(common)
        necessary = (Fraction(total*total, nodes_left)-(2*len(fs)-1)*total
                     + len(fs)*(len(fs)-1)*pair_union)
        assert necessary <= 0
    return {"members": len(fs), "exact_error_degrees": list(map(len, errors)),
            "locator_rank": dimension, "rank_bound": 4**(dimension-1),
            "common_errors": len(common), "maximum_other_incidence": maximal_incidence}


def main():
    identities = exact_identities()
    cases = endpoint_checks()
    p, nodes, shared, word, fs = four_member_fixture()
    sharp = check_family(p, nodes, 4, word, fs)
    assert sharp["locator_rank"] == 2 and sharp["exact_error_degrees"] == [6]*4
    heterogeneous_word = dict(word)
    heterogeneous_word[shared] = evaluate(fs[0], shared, p)
    heterogeneous = check_family(p, nodes, 4, heterogeneous_word, fs)
    assert heterogeneous["locator_rank"] == 3
    assert heterogeneous["exact_error_degrees"] == [5, 6, 6, 6]
    endpoint = check_family(p, nodes, 4, dict.fromkeys(nodes, 0), [[0]])
    assert endpoint["locator_rank"] == 1 and endpoint["exact_error_degrees"] == [0]
    n = 2**30
    assert 6*178956971-2 == n and 4**15 == n and 4**16 > n
    print(json.dumps({
        "status": "PASS_LOCATOR_RANK_IDENTITIES_AND_EXACT_ERROR_CONTROLS",
        "integer_polynomial_identities": identities, "rational_endpoint_cases": cases,
        "F101_sharp_rank_two_family": sharp,
        "F101_heterogeneous_family": heterogeneous, "rank_one_endpoint": endpoint,
        "conditional_rank_sixteen_budget": n,
        "universal_rank_sixteen_proved": False, "new_lean_verification": False,
        "prize_solved": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
