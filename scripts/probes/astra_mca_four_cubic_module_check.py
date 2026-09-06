#!/usr/bin/env python3
"""Exact coefficient-space certificate for the four-cubic coincidence geometry."""
import json
from astra_mca_four_cubic_check import P, N, seeds, ev


def reduce_rows(matrix):
    rows = [row[:] for row in matrix]
    pivots = []
    for column in range(len(rows[0])):
        position = len(pivots)
        pivot = next((i for i in range(position, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[position], rows[pivot] = rows[pivot], rows[position]
        inverse = pow(rows[position][column], -1, P)
        rows[position] = [value * inverse % P for value in rows[position]]
        for i in range(len(rows)):
            if i != position:
                scale = rows[i][column]
                rows[i] = [(a - scale * b) % P for a, b in zip(rows[i], rows[position])]
        pivots.append(column)
    return rows, pivots


def kernel(matrix):
    rows, pivots = reduce_rows(matrix)
    width = len(matrix[0])
    basis = []
    for free in range(width):
        if free in pivots:
            continue
        vector = [0] * width
        vector[free] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -rows[i][free] % P
        assert all(sum(a * b for a, b in zip(row, vector)) % P == 0 for row in matrix)
        basis.append(vector)
    return basis, pivots


def constraints(degree, nodes):
    relations = [(0, 1, 0), (0, 2, 0), (1, 1, 0), (1, 3, 0),
                 (3, 2, 0), (3, 3, 0), (6, 1, 2), (6, 1, 3),
                 (7, 1, 2), (7, 1, 3)]
    rows = []
    for j, left, right in relations:
        row = [0] * (3 * (degree + 1))
        for index, sign in [(left, 1), (right, -1)]:
            if index:
                for power in range(degree + 1):
                    position = (index - 1) * (degree + 1) + power
                    row[position] = (row[position] + sign * pow(nodes[j], power, P)) % P
        rows.append(row)
    return rows


def verify():
    _, nodes, sources = seeds()
    cubic_matrix = constraints(3, nodes)
    basis, pivots = kernel(cubic_matrix)
    assert len(pivots) == 10 and len(basis) == 2
    quadratic_matrix = constraints(2, nodes)
    quadratic_basis, quadratic_pivots = kernel(quadratic_matrix)
    assert len(quadratic_pivots) == 9 and not quadratic_basis
    original = [c for polynomial in sources[1:] for c in polynomial]
    assert all(sum(a * b for a, b in zip(row, original)) % P == 0 for row in cubic_matrix)
    alternative = next(vector for vector in basis if len(reduce_rows([original, vector])[1]) == 2)
    expanded = [[0]] + [alternative[4 * i:4 * i + 4] for i in range(3)]
    residuals = [ev(expanded[index], nodes[j]) for j, index in [(2, 3), (4, 2), (5, 1)]]
    assert all(residuals)
    assert all(ev(sources[index], nodes[j]) == 0 for j, index in [(2, 3), (4, 2), (5, 1)])
    leading_rows = [[sources[i][3], expanded[i][3]] for i in range(1, 4)]
    assert len(reduce_rows(leading_rows)[1]) == 2
    s = N // 8
    root_degree = s - 2
    multiplier_degree = 4 * s - 1 - root_degree - 3 * s
    covered_pair_nodes = 3 * s // 2
    assert multiplier_degree == 1 and covered_pair_nodes > multiplier_degree
    return {
        'status': 'PASS_EXACT_FOUR_CUBIC_MODULE_CERTIFICATE',
        'prime': P,
        'cubic_constraint_rank': 10,
        'cubic_coefficient_dimension': 12,
        'quadratic_constraint_rank': 9,
        'quadratic_coefficient_dimension': 9,
        'cubic_pivots': pivots,
        'quadratic_pivots': quadratic_pivots,
        'original_basis_vector': sources,
        'independent_basis_vector': expanded,
        'pair_fiber_residuals': residuals,
        'leading_coefficient_rank': 2,
        'production_multiplier_degree': multiplier_degree,
        'production_covered_pair_nodes': covered_pair_nodes,
        'scope': 'Exact eight-node coefficient-space certificate plus written power-residue '
                 'and polynomial root-bound argument. Not Lean formalization or a universal MCA bound.'
    }


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
