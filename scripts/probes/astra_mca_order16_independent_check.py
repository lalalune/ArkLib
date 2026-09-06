#!/usr/bin/env python3
"""Independent exact linear-system reconstruction and dense MCA controls.

Uses only the standard library. The four polynomials are reconstructed from
24 triple-agreement equations, independently of the factored primary seed.
Dense words are controls at smaller domains over the actual production field;
the production-sized conclusion uses the written lifting/counting argument.
"""

from fractions import Fraction
import json

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
TRIPLES = (((0, 5, 13), (0, 1, 2)), ((1, 8, 9), (0, 1, 3)),
           ((3, 11, 12), (0, 2, 3)), ((4, 7, 15), (1, 2, 3)))


def evaluate(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = (value * x + coefficient) % P
    return value


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            result[i + j] = (result[i + j] + ai * bj) % P
    return result


def reconstruct():
    eta = pow(G, N // 16, P)
    assert pow(eta, 16, P) == 1 and pow(eta, 8, P) != 1
    rows = []
    for exponents, owners in TRIPLES:
        for exponent in exponents:
            x = pow(eta, exponent, P)
            for other in owners[1:]:
                row = [0] * 24
                for source, sign in ((owners[0], -1), (other, 1)):
                    if source:
                        for degree in range(8):
                            row[8 * (source - 1) + degree] += sign * pow(x, degree, P)
                rows.append([entry % P for entry in row])
    rank = 0
    pivots = []
    for column in range(24):
        pivot = next((r for r in range(rank, 24) if rows[r][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, P)
        rows[rank] = [entry * inverse % P for entry in rows[rank]]
        for r in range(24):
            if r != rank:
                coefficient = rows[r][column]
                rows[r] = [(a - coefficient * b) % P
                           for a, b in zip(rows[r], rows[rank])]
        pivots.append(column)
        rank += 1
    assert rank == 23, rank
    free = next(c for c in range(24) if c not in pivots)
    vector = [0] * 24
    vector[free] = 1
    for r, column in enumerate(pivots):
        vector[column] = -rows[r][free] % P
    # Normalize W1 monic, allowing a direct comparison to the primary fixture.
    inverse = pow(vector[7], -1, P)
    vector = [entry * inverse % P for entry in vector]
    seed = [[0]] + [vector[8*i:8*i+8] for i in range(3)]
    partitions = []
    for j in range(16):
        groups = {}
        for source, poly in enumerate(seed):
            groups.setdefault(evaluate(poly, pow(eta, j, P)), []).append(source)
        partitions.append(list(groups.values()))
    for exponents, owners in TRIPLES:
        for j in exponents:
            assert list(owners) in partitions[j]
    assert partitions[2] == [[0], [1], [2], [3]]
    assert partitions[6] == [[0, 1], [2], [3]]
    assert partitions[10] == [[0, 3], [1, 2]]
    assert partitions[14] == [[0], [1], [2, 3]]
    return seed, rank


def allocation(s):
    assert s % 6 == 4
    t = (s - 4) // 6
    roots = {2: 4*t + 2, 6: t, 14: t}
    owners = {j: list(group) for exponents, group in TRIPLES for j in exponents}
    return t, roots, owners


def dense_control(n, seed):
    assert N % n == 0 and n % 16 == 0
    s, k = n // 16, n // 2
    t, root_counts, triple_owners = allocation(s)
    generator = pow(G, N // n, P)
    coordinates = [(j, a, pow(generator, j + 16*a, P))
                   for j in range(16) for a in range(s)]
    assert len({x for _, _, x in coordinates}) == n
    roots = {x for j, a, x in coordinates if a < root_counts.get(j, 0)}
    assert len(roots) == s-2
    locator = [1]
    for x in sorted(roots):
        locator = multiply(locator, [-x % P, 1])
    polynomials = []
    for poly in seed:
        composed = [0] * ((len(poly)-1) * s + 1)
        for degree, coefficient in enumerate(poly):
            composed[degree*s] = coefficient
        polynomials.append(multiply(locator, composed))
    assert all(len(poly) - 1 <= k-2 for poly in polynomials)
    values = {x: [evaluate(poly, x) for poly in polynomials] for _, _, x in coordinates}
    word, covered, uncovered = {}, [], []
    for j, a, x in coordinates:
        if x in roots:
            assert values[x] == [0]*4
            word[x] = (0, 0)
        elif j == 2:
            assert len(set(values[x])) == 4
            uncovered.append(x)
        else:
            owners = triple_owners.get(j)
            if owners is None:
                owners = [0, 1] if j == 6 else [2, 3] if j == 14 else (
                    [0, 3] if a < s//2 else [1, 2])
            z = values[x][owners[0]]
            assert [i for i, v in enumerate(values[x]) if v == z] == owners
            word[x] = (z, x*z % P)
            covered.append(x)
    ordinary = {-pow(x, -1, P) % P for x in covered}
    assert len(ordinary) == len(covered)
    blocked = set(ordinary)
    witnesses = []
    for x in covered:
        source = next(i for i in range(4) if values[x][i] != word[x][0])
        witnesses.append((-pow(x, -1, P) % P, x, source))
    for x in uncovered:
        a = next(a for a in range(5) if a not in values[x])
        b = 0
        while True:
            if b != x*a % P and all(b != x*z % P for z in values[x]):
                directions = [(z-a) * pow((b-x*z) % P, -1, P) % P for z in values[x]]
                if len(set(directions)) == 4 and not blocked.intersection(directions):
                    break
            b += 1
        word[x] = (a, b)
        blocked.update(directions)
        witnesses.extend((gamma, x, i) for i, gamma in enumerate(directions))
    cores = [{x for _, _, x in coordinates if word[x] == (values[x][i], x*values[x][i] % P)}
             for i in range(4)]
    core_size = 68*t+44
    assert [len(core) for core in cores] == [core_size]*4
    assert core_size >= k
    assert len(blocked) == len(witnesses) == n+4
    for gamma, origin, source in witnesses:
        assert origin not in cores[source]
        agreement = {x for _, _, x in coordinates
                     if (word[x][0] + gamma*word[x][1] -
                         (1+gamma*x)*values[x][source]) % P == 0}
        assert agreement == cores[source] | {origin}
        # Any joint code pair on this same support must equal our source pair:
        # both coordinate differences have degree <k and >=k distinct zeros.
        # The nonzero residual at origin therefore excludes every such pair.
        assert word[origin] != (values[origin][source], origin*values[origin][source] % P)
    return {"n": n, "k": k, "root_count": len(roots), "core_sizes": [len(c) for c in cores],
            "ordinary_count": len(ordinary), "fresh_count": len(blocked)-len(ordinary),
            "distinct_bad_scalars": len(blocked), "support_size": core_size+1,
            "exact_all_agreement_sets_checked": True,
            "no_joint_basis": "full-code polynomial root bound, degree < k and core >= k"}


def main():
    assert pow(G, N, P) == 1 and pow(G, N//2, P) != 1
    seed, rank = reconstruct()
    s = N//16
    t, roots, _ = allocation(s)
    core = 68*t+44
    ordinary = 15*s-2*t
    uncovered = s-roots[2]
    assert sum(roots.values()) == s-2
    assert ordinary + 4*uncovered == N+4
    radius = Fraction(N-core-1, N)
    assert radius == Fraction(7, 24) + Fraction(1, 3*N)
    assert (N+4)*2**128 > P
    assert P > 4*(N+5)+1
    print(json.dumps({"status": "PASS_INDEPENDENT_ORDER16_RECONSTRUCTION_AND_DENSE_CONTROLS",
                      "seed_constraint_rank": rank, "seed_polynomials": seed,
                      "production": {"n": N, "core": core, "support": core+1,
                                     "bad_scalar_lower_count": N+4,
                                     "radius": str(radius), "radius_decimal": float(radius)},
                      "dense_controls": [dense_control(n, seed) for n in (64, 256)]}, indent=2))


if __name__ == "__main__":
    main()
