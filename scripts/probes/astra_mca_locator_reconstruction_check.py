#!/usr/bin/env python3
"""Exact controls for the full-domain balanced-locator reconstruction converse.

This is not a production witness or an exclusion. Standard library only.
"""
import itertools
import json

P30 = 365375409332725729550921208179070755120141565953
G30 = 303645430271030343624574566109998498685964493478
P = P30


def trim(a):
    a = [v % P for v in a]
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a or [0]


def add(a, b, scale=1):
    return trim([(a[i] if i < len(a) else 0) +
                 scale * (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def ev(a, x):
    out = 0
    for y in reversed(a):
        out = (out*x+y) % P
    return out


def divexact(a, b):
    a = trim(a)
    out = [0] * max(1, len(a)-len(b)+1)
    while a != [0] and len(a) >= len(b):
        d = len(a)-len(b)
        c = a[-1]*pow(b[-1], -1, P) % P
        out[d] = c
        a = add(a, [0]*d+[c*x % P for x in b], -1)
    assert a == [0]
    return trim(out)


def dot(a, b):
    out = [0]
    for x, y in zip(a, b):
        out = add(out, mul(x, y))
    return out


def cross(a, b):
    return [add(mul(a[(i+1)%3], b[(i+2)%3]),
                mul(a[(i+2)%3], b[(i+1)%3]), -1) for i in range(3)]


def locator(roots):
    out = [1]
    for x in roots:
        out = mul(out, [-x, 1])
    return out


def rank(rows):
    rows = [row[:] for row in rows]
    pivot = 0
    for col in range(len(rows[0])):
        j = next((j for j in range(pivot, len(rows)) if rows[j][col]), None)
        if j is None:
            continue
        rows[j], rows[pivot] = rows[pivot], rows[j]
        inv = pow(rows[pivot][col], -1, P)
        rows[pivot] = [v*inv % P for v in rows[pivot]]
        for j in range(pivot+1, len(rows)):
            s = rows[j][col]
            rows[j] = [(x-s*y) % P for x, y in zip(rows[j], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def solve(rows, values):
    """Return one solution, setting free variables to zero, and matrix rank."""
    a = [[x % P for x in row] + [v % P] for row, v in zip(rows, values)]
    r = 0
    pivots = []
    for c in range(len(rows[0])):
        j = next((j for j in range(r, len(a)) if a[j][c]), None)
        if j is None:
            continue
        a[j], a[r] = a[r], a[j]
        inv = pow(a[r][c], -1, P)
        a[r] = [x*inv % P for x in a[r]]
        for j in range(len(a)):
            if j != r:
                s = a[j][c]
                a[j] = [(x-s*y) % P for x, y in zip(a[j], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    assert all(any(row[:-1]) or not row[-1] for row in a)
    out = [0]*len(rows[0])
    for j, c in enumerate(pivots):
        out[c] = a[j][-1]
    return out, r


def reconstruct(b, omega, B, C, points):
    n, k, d = 6*b-2, 3*b-1, 3*b-2
    assert len(omega) == n == len(set(omega))
    V = locator(omega)
    w = cross(B, C)
    assert max(map(len, w)) == 2*b+1
    balance_columns = [[0]*j+wj for wj in w for j in range(b)]
    balance_matrix = [[col[i] if i < len(col) else 0 for col in balance_columns]
                      for i in range(3*b)]
    balance_rank = rank(balance_matrix)
    assert balance_rank == 3*b
    t = 4*b-2
    columns = [[0]*j+wj for wj in w for j in range(t+1)]
    matrix = [[col[i] if i < len(col) else 0 for col in columns]
              for i in range(n+1)]
    coefficients, bezout_rank = solve(matrix, V)
    assert bezout_rank == n+1
    A = [trim(coefficients[i*(t+1):(i+1)*(t+1)]) for i in range(3)]
    assert dot(A, w) == V
    ca, ab = cross(C, A), cross(A, B)
    M = [[w[i], ca[i], ab[i]] for i in range(3)]
    N = [A, B, C]
    for i in range(3):
        for j in range(3):
            assert dot(N[i], [M[r][j] for r in range(3)]) == (V if i == j else [0])
    assert dot(M[0], cross(M[1], M[2])) == mul(V, V)
    pairs, locators = [], []
    for c in points:
        q = [dot([[x] for x in c], [M[i][j] for i in range(3)]) for j in range(3)]
        W = q[0]
        assert len(W) == 2*b+1 and W[-1] == 1
        assert sum(ev(W, x) == 0 for x in omega) == 2*b
        divexact(V, W)
        pair = [divexact(q[j], W) for j in (1, 2)]
        assert all(len(f) <= d+1 for f in pair)
        pairs.append(pair)
        locators.append(W)
    received = []
    for x in omega:
        owners = [i for i, W in enumerate(locators) if ev(W, x)]
        assert owners
        u = tuple(ev(f, x) for f in pairs[owners[0]])
        assert all(tuple(ev(f, x) for f in pairs[i]) == u for i in owners)
        received.append(u)
    directions, witnesses = [], 0
    for i, ((f, g), W) in enumerate(zip(pairs, locators)):
        slots = {}
        exact_core = []
        for pos, x in enumerate(omega):
            e = ((ev(f, x)-received[pos][0]) % P,
                 (ev(g, x)-received[pos][1]) % P)
            assert (e == (0, 0)) == (ev(W, x) != 0)
            if e == (0, 0):
                exact_core.append(pos)
                continue
            direction = -e[0]*pow(e[1], -1, P) % P if e[1] else None
            slots.setdefault(direction, []).append(pos)
            # Independently check the differentiated adjugate direction identity.
            combined = [(e[0]*ev(B[j], x)+e[1]*ev(C[j], x)) % P for j in range(3)]
            assert rank([combined, list(points[i])]) == 1
        assert len(exact_core) == 4*b-2
        bad = {s for s, positions in slots.items() if s is not None and len(positions) >= 2}
        for gamma in bad:
            support = [j for j, x in enumerate(omega)
                       if (ev(f, x)+gamma*ev(g, x)-received[j][0]-gamma*received[j][1]) % P == 0]
            assert len(support) >= 4*b and set(exact_core) <= set(support)
            extra = [j for j in support if j not in exact_core]
            target_support = list(exact_core) + extra[:2]
            assert len(target_support) == 4*b
            # Check both the exact target support and the full agreement set.
            for checked_support in (target_support, support):
                vand = [[pow(omega[j], l, P) for l in range(k)] for j in checked_support]
                vrank = rank(vand)
                assert vrank == k
                # Original same-support no-joint clause, by exact linear rank.
                assert any(rank([row+[received[j][q]] for row, j in zip(vand, checked_support)]) > vrank
                           for q in (0, 1))
            witnesses += 1
        directions.append((bad, sorted(map(len, slots.values()))))
    # Any bounded choice of the Bezout row only globally translates the pair.
    a, c = [2, 3]+[0]*(d-1)+[1], [5, 7]
    a = trim(a[:d+1])
    A2 = [add(add(A[j], mul(a, B[j])), mul(c, C[j])) for j in range(3)]
    assert max(map(len, A2)) <= t+1 and dot(A2, w) == V
    ca2, ab2 = cross(C, A2), cross(A2, B)
    for j in range(3):
        assert ca2[j] == add(ca[j], mul(a, w[j]), -1)
        assert ab2[j] == add(ab[j], mul(c, w[j]), -1)
    return {"b": b, "n": n, "field": P, "pencil_count": len(points),
            "bezout_matrix_rank": bezout_rank, "bezout_columns": len(columns),
            "balanced_square_matrix_rank": balance_rank,
            "exact_core_size": 4*b-2, "per_pencil_slot_multiplicities": [a[1] for a in directions],
            "checked_MCA_witnesses": witnesses,
            "distinct_finite_bad_scalars": len(set().union(*(a[0] for a in directions)))}


def case(b, p, generator):
    global P
    P = p
    roots = [pow(generator, j, P) for j in range(4*b)]
    assert len(set(roots)) == 4*b and pow(generator, 4*b, P) == 1
    image = sorted({pow(x, b, P) for x in roots})
    assert len(image) == 4
    omega = roots[:]
    candidate = 0
    while len(omega) < 6*b-2:
        if candidate not in omega:
            omega.append(candidate)
        candidate += 1
    xb = [0]*b+[1]
    B, C = [[1], xb, [0]], [[0], [1], xb]
    points = [(1, (r+s) % P, r*s % P) for r, s in itertools.combinations(image, 2)]
    return reconstruct(b, omega, B, C, points)


if __name__ == "__main__":
    out = [case(1, P30, pow(G30, 2**30//4, P30)),
           case(2, P30, pow(G30, 2**30//8, P30)),
           case(3, 37, pow(2, 3, 37)),
           case(4, P30, pow(G30, 2**30//16, P30))]
    assert all(x["distinct_finite_bad_scalars"] == (0 if x["b"] == 1 else 4) for x in out)
    print(json.dumps({"status": "PASS_BALANCED_DOMAIN_LOCATOR_CONVERSE", "cases": out,
                      "production_witness": False, "production_exclusion": False}, indent=2))
