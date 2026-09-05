#!/usr/bin/env python3
"""Exact checks of the four-coset syzygy obstruction in the production field.

Only one recursively balanced partition is evaluated at each small domain.
The general all-splits result is proved in the paired note, not inferred from
these finite checks. No claim covers arbitrary partitions of the full domain.
"""

P = 365375409332725729550921208179070755120141565953


def multiply(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % P
    return c


def vanishing(roots):
    result = [1]
    for root in roots:
        result = multiply(result, [-root % P, 1])
    return result


def rank(matrix):
    a = [row[:] for row in matrix]
    rows, columns = len(a), len(a[0])
    pivot_row = 0
    for column in range(columns):
        pivot = next((i for i in range(pivot_row, rows) if a[i][column]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inverse = pow(a[pivot_row][column], -1, P)
        a[pivot_row][column:] = [x*inverse % P for x in a[pivot_row][column:]]
        for i in range(pivot_row+1, rows):
            multiple = a[i][column]
            if multiple:
                a[i][column:] = [(x-multiple*y) % P
                    for x, y in zip(a[i][column:], a[pivot_row][column:])]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def label(exponent, n):
    # First base-four digit other than3 picks a region; the all-3 word goes C.
    if exponent == n-1:
        return 2
    while exponent % 4 == 3:
        exponent //= 4
    return exponent % 4


def check(n):
    assert (P-1) % n == 0
    omega = next(value for base in range(2, 100)
        if (value := pow(base, (P-1)//n, P)) and pow(value, n//2, P) != 1)
    assert pow(omega, n, P) == 1
    nodes = [pow(omega, exponent, P) for exponent in range(n)]
    assert len(set(nodes)) == n
    regions = [[nodes[e] for e in range(n) if label(e,n) == j] for j in range(3)]
    assert list(map(len,regions)) == [(n-1)//3, (n-1)//3, (n+2)//3]
    m = n//4
    residual = [[nodes[e] for e in range(n) if e%4 == 3 and label(e,n) == j]
                for j in range(3)]
    small = [vanishing(roots) for roots in residual]
    whole = [vanishing(roots) for roots in regions]
    coset_values = [pow(omega,j*m,P) for j in range(4)]
    assert len(set(coset_values)) == 4
    for j in range(3):
        factor = [-coset_values[j] % P]+[0]*(m-1)+[1]
        assert whole[j] == multiply(factor,small[j])
    residual_product = multiply(multiply(small[0],small[1]),small[2])
    assert residual_product == [-coset_values[3] % P]+[0]*(m-1)+[1]
    outcomes = []
    for degree in (2*m-2, 2*m-1, 2*m):
        columns = [(f, shift) for f in whole
                   for shift in range(max(0,degree-len(f)+2))]
        matrix = [[f[k-shift] if 0 <= k-shift < len(f) else 0
                   for f,shift in columns] for k in range(degree+1)]
        dimension = len(columns)-rank(matrix)
        assert dimension == (2 if degree == 2*m else 0)
        outcomes.append((degree, len(columns), dimension))
    return {"n":n,"primitive_root":omega,"region_sizes":list(map(len,regions)),
            "degree_columns_nullity":outcomes,"minimal_product_degree":2*m}


def main():
    import json
    for n in (4,16,64,256):
        print(json.dumps(check(n),sort_keys=True))
    n = 2**30
    a, b, c = 0,0,1
    for _ in range(15):
        m = a+b+c
        a,b,c = m+a,m+b,m+c
    assert (a,b,c) == ((n-1)//3,(n-1)//3,(n+2)//3)
    assert 4*m == n
    print(json.dumps({"production_n":n,"balanced_recursive_sizes":[a,b,c],
        "four_coset_minimum_by_general_proof":n//2,
        "attack_degree_cap":n//2-2,"status":"ARCHITECTURE_EXCLUDED_NOT_ARBITRARY_PARTITIONS"},
        sort_keys=True))


if __name__ == "__main__":
    main()
