#!/usr/bin/env python3
"""Exact finite controls for linear projection and preservation of list budgets.

Written proof: docs/kb/astra_interleaved_projection-2026-09-05.md.
This checks small instances and production arithmetic, not a production list bound.
"""

from collections import Counter
from itertools import combinations, product
from math import comb
import json


class Field:
    """Prime fields, plus F4=F2[t]/(t^2+t+1)."""

    def __init__(self, q):
        assert q in (2, 3, 4, 5, 7)
        self.q = q

    def add(self, a, b):
        return a ^ b if self.q == 4 else (a+b) % self.q

    def neg(self, a):
        return a if self.q == 4 else -a % self.q

    def mul(self, a, b):
        if self.q != 4:
            return a*b % self.q
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return out

    def inv(self, a):
        assert a
        return next(b for b in range(1, self.q) if self.mul(a, b) == 1)

    def sum(self, xs):
        out = 0
        for x in xs:
            out = self.add(out, x)
        return out


def rank(rows, field):
    a = [list(row) for row in rows]
    if not a:
        return 0
    pivot_row = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(pivot_row, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inverse = field.inv(a[pivot_row][col])
        a[pivot_row] = [field.mul(inverse, x) for x in a[pivot_row]]
        for j in range(len(a)):
            if j != pivot_row and a[j][col]:
                factor = a[j][col]
                a[j] = [field.add(x, field.neg(field.mul(factor, y)))
                        for x, y in zip(a[j], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def project(columns, lam, field):
    return tuple(field.sum(field.mul(c, column[i])
                           for c, column in zip(lam, columns))
                 for i in range(len(columns[0])))


def field_check(field):
    elems = range(field.q)
    for a, b, c in product(elems, repeat=3):
        assert field.add(a, b) == field.add(b, a)
        assert field.mul(a, b) == field.mul(b, a)
        assert field.mul(a, field.add(b, c)) == field.add(
            field.mul(a, b), field.mul(a, c))
        assert field.mul(a, field.mul(b, c)) == field.mul(field.mul(a, b), c)
        assert field.add(a, field.add(b, c)) == field.add(field.add(a, b), c)
    for a in elems:
        assert field.add(a, field.neg(a)) == 0
        assert field.mul(a, 1) == a
        if a:
            assert field.mul(a, field.inv(a)) == 1


def separation_check(family, field):
    """Exhaust all coefficient vectors; compare collision counts to matrix rank."""
    m = len(family[0])
    n = len(family[0][0])
    assert len(set(family)) == len(family)
    lambdas = tuple(product(range(field.q), repeat=m))
    bad_union = set()
    ranks = Counter()
    rank_union_bound = 1
    for a, b in combinations(family, 2):
        rows = [[field.add(a[j][i], field.neg(b[j][i])) for j in range(m)]
                for i in range(n)]
        r = rank(rows, field)
        assert r >= 1
        bad = {lam for lam in lambdas if project(a, lam, field) == project(b, lam, field)}
        assert len(bad) == field.q**(m-r)
        rank_union_bound += len(bad)-1
        bad_union |= bad
        ranks[r] += 1
    good = [lam for lam in lambdas if len({project(a, lam, field) for a in family}) == len(family)]
    assert len(good)+len(bad_union) == field.q**m
    assert len(bad_union) <= rank_union_bound
    h = comb(len(family), 2)
    if h <= field.q:
        assert rank_union_bound < field.q**m and good
    return {"q": field.q, "m": m, "M": len(family), "pairs": h,
            "difference_ranks": dict(sorted(ranks.items())),
            "bad_coefficients": len(bad_union), "good_coefficients": len(good)}


def linear_code(field, generator):
    k = len(generator)
    n = len(generator[0])
    assert rank(generator, field) == k
    return tuple(tuple(field.sum(field.mul(c, generator[j][i])
                                  for j, c in enumerate(coeffs)) for i in range(n))
                 for coeffs in product(range(field.q), repeat=k))


def list_maximum(field, code, m, errors, observable=None):
    """Count all received-word lists by enumerating every codeword's Hamming ball."""
    n = len(code[0])
    alphabet = tuple(product(range(field.q), repeat=m))
    centers = Counter()
    observed = {} if observable is not None else None
    for columns in product(code, repeat=m):
        rows = tuple(tuple(column[i] for column in columns) for i in range(n))
        if observable is not None:
            values = tuple(observable(column) for column in columns)
        for e in range(errors+1):
            for changed in combinations(range(n), e):
                alternatives = [tuple(a for a in alphabet if a != rows[i]) for i in changed]
                for replacements in product(*alternatives):
                    center = list(rows)
                    for i, replacement in zip(changed, replacements):
                        center[i] = replacement
                    key = tuple(center)
                    centers[key] += 1
                    if observed is not None:
                        observed.setdefault(key, set()).add(values)
    if observed is not None:
        return max(centers.values()), max(map(len, observed.values()))
    return max(centers.values()), len(centers)


def projection_membership_control(field, code, m, errors):
    """Directly check projected list membership and scalar-code closure on all tuples."""
    n = len(code[0])
    alphabet = tuple(product(range(field.q), repeat=m))
    code_set = set(code)
    checks = 0
    for center in product(alphabet, repeat=n):
        center_columns = tuple(tuple(row[j] for row in center) for j in range(m))
        candidates = []
        for columns in product(code, repeat=m):
            rows = tuple(tuple(column[i] for column in columns) for i in range(n))
            if sum(a != b for a, b in zip(rows, center)) <= errors:
                candidates.append(columns)
        for lam in product(range(field.q), repeat=m):
            scalar_center = project(center_columns, lam, field)
            for columns in candidates:
                scalar = project(columns, lam, field)
                assert scalar in code_set
                assert sum(a != b for a, b in zip(scalar, scalar_center)) <= errors
                checks += 1
    return checks


def production_gates():
    prime = 365375409332725729550921208179070755120141565953
    n = 2**30
    assert prime == n*(2**128+192)+1
    records = []
    for name, q in (("grand_production", prime), ("companion", 2130706433**6)):
        budget = q//2**128
        pairs = comb(budget+1, 2)
        assert pairs <= q and 1 <= budget < q
        rounded_collision_bound = budget*(q-1)//(q-budget)
        assert rounded_collision_bound == budget
        records.append({"profile": name, "q": q, "budget": budget,
                        "pair_bound": pairs, "gate_margin": q-pairs,
                        "rounded_collision_bound": rounded_collision_bound})
    assert records[0]["budget"] == n
    assert records[0]["pair_bound"] == 576460752840294400
    assert records[1]["budget"] == 274980728111395087
    return records


def main():
    fields = {q: Field(q) for q in (2, 3, 4, 5, 7)}
    for field in fields.values():
        field_check(field)
    # Rank-one equality gate q=3=choose(3,2), with two separating coefficients.
    boundary = separation_check((((0,), (0,)), ((1,), (0,)), ((0,), (1,))), fields[3])
    assert boundary["bad_coefficients"] == 7 and boundary["good_coefficients"] == 2
    # The same family is checked over an extension field, then with rank-two differences.
    extension = separation_check((((0,), (0,)), ((1,), (0,)), ((0,), (1,))), fields[4])
    rank_two = separation_check((((0, 0), (0, 0)), ((1, 0), (0, 1)),
                                 ((0, 1), (1, 1))), fields[3])
    assert rank_two["difference_ranks"].get(2, 0) > 0
    obstruction = separation_check(tuple(((a,), (b,)) for a, b in
                                         ((0, 0), (1, 0), (0, 1), (2, 2))), fields[5])
    assert obstruction["good_coefficients"] == 0

    list_controls = []
    cases = ((3, ((1, 1),), 1, (1, 2, 3)),
             (4, ((1, 1),), 1, (1, 2)),
             (7, ((1, 1, 1), (0, 1, 2)), 1, (1, 2)),
             (2, ((1, 0), (0, 1)), 1, (1, 2)))
    for q, generator, errors, arities in cases:
        field = fields[q]
        code = linear_code(field, generator)
        maxima = {}
        covered = {}
        for m in arities:
            maxima[m], covered[m] = list_maximum(field, code, m, errors)
        bound = maxima[1]
        gate = comb(bound+1, 2) <= q
        if gate:
            assert all(value == bound for value in maxima.values())
        if bound < q:
            assert all(value <= bound*(q-1)//(q-bound) for value in maxima.values())
        list_controls.append({"q": q, "n": len(generator[0]), "k": len(generator),
                              "errors": errors, "maxima_by_arity": maxima,
                              "covered_centers_by_arity": covered, "field_gate": gate})
    assert list_controls[0]["maxima_by_arity"] == {1: 2, 2: 2, 3: 2}
    assert list_controls[2]["maxima_by_arity"] == {1: 3, 2: 3}
    assert list_controls[3]["maxima_by_arity"] == {1: 3, 2: 7}
    membership_checks = projection_membership_control(fields[3], linear_code(fields[3], ((1, 1),)), 2, 1)
    feature_code = linear_code(fields[3], ((1, 1, 1, 0), (0, 0, 0, 1)))
    observable_controls = {m: list_maximum(fields[3], feature_code, m, 1, lambda c: c[0])
                           for m in (1, 2)}
    assert observable_controls == {1: (3, 1), 2: (9, 1)}
    print(json.dumps({"status": "PASS_INTERLEAVED_PROJECTION_TRANSFER_CONTROLS",
                      "production_gates": production_gates(),
                      "separation_controls": [boundary, extension, rank_two, obstruction],
                      "list_controls": list_controls,
                      "direct_projection_membership_checks": membership_checks,
                      "observable_control_full_list_and_value_maxima": observable_controls,
                      "production_scalar_bound_proved": False,
                      "lean_run_performed": False}, indent=2))


if __name__ == "__main__":
    main()
