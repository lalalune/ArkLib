import itertools, cmath, math
from collections import defaultdict

def roots_of_unity(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def close(z, tol=1e-7):
    return abs(z.real) < tol and abs(z.imag) < tol

def multiset_eq(A, B, tol=1e-6):
    B = list(B)
    for a in A:
        found = False
        for i, b in enumerate(B):
            if abs(a - b) < tol:
                B.pop(i); found = True; break
        if not found:
            return False
    return True

def esymm(vals, h):
    es = [0j] * (h + 1)
    es[0] = 1 + 0j
    for v in vals:
        for k in range(h, 0, -1):
            es[k] += es[k-1] * v
    return es[1:]   # e_1 .. e_h

def test_n(n, h):
    R = roots_of_unity(n)
    tuples = list(itertools.combinations_with_replacement(range(n), h))

    # signature by sum (e_1) only
    by_sum = defaultdict(list)
    for t in tuples:
        s = sum(R[i] for i in t)
        if close(s):
            continue
        key = (round(s.real, 6), round(s.imag, 6))
        by_sum[key].append(t)
    sum_collisions = 0; sum_pairs = 0
    for ts in by_sum.values():
        for a, b in itertools.combinations(ts, 2):
            sum_pairs += 1
            if not multiset_eq([R[i] for i in a], [R[i] for i in b]):
                sum_collisions += 1

    # signature by e_1 .. e_{h-1}  (all elementary symmetric except the product e_h)
    by_e = defaultdict(list)
    for t in tuples:
        es = esymm([R[i] for i in t], h)
        if close(es[0]):
            continue
        key = tuple(round(x.real, 6) for x in es[:h-1]) + tuple(round(x.imag, 6) for x in es[:h-1])
        by_e[key].append(t)
    e_collisions = 0; e_pairs = 0
    for ts in by_e.values():
        for a, b in itertools.combinations(ts, 2):
            e_pairs += 1
            if not multiset_eq([R[i] for i in a], [R[i] for i in b]):
                e_collisions += 1

    return sum_collisions, sum_pairs, e_collisions, e_pairs

for n in [4, 8, 16]:
    for h in [2, 3]:
        sc, sp, ec, ep = test_n(n, h)
        print(f"n={n:3d} h={h}: SUM-only collisions={sc}/{sp} pairs | e_1..e_{{h-1}} collisions={ec}/{ep} pairs")
