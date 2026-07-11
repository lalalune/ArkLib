#!/usr/bin/env python3
"""Probe the B_h-Sidon list bridge: equal ordered h-tuples over a B_h set are permutations.

This is finite abelian Z/m sanity checking for the Lean lemma
IsBhSidon.list_perm_of_sum_eq.  It deliberately checks proper small sets in cyclic
ambient groups, not full multiplicative groups or prize CORE claims.
"""
from itertools import combinations, product
from collections import Counter


def is_bh_sidon(S, h, m):
    # h-fold multisets represented by nondecreasing index tuples
    def gen(start, depth):
        if depth == 0:
            yield ()
        else:
            for i in range(start, len(S)):
                for rest in gen(i, depth - 1):
                    yield (i,) + rest
    seen = {}
    for idxs in gen(0, h):
        vals = tuple(S[i] for i in idxs)
        s = sum(vals) % m
        if s in seen and Counter(vals) != Counter(seen[s]):
            return False
        seen[s] = vals
    return True


def main():
    checked_sets = checked_pairs = fails = 0
    for m in [17, 19, 23, 29, 31]:
        elems = list(range(m))
        for size in range(1, 5):
            for S_tuple in combinations(elems, size):
                S = list(S_tuple)
                for h in [1, 2, 3]:
                    if not is_bh_sidon(S, h, m):
                        continue
                    checked_sets += 1
                    tuples = list(product(S, repeat=h))
                    for a in tuples:
                        suma = sum(a) % m
                        ca = Counter(a)
                        for b in tuples:
                            if sum(b) % m == suma:
                                checked_pairs += 1
                                if Counter(b) != ca:
                                    print("FAIL", m, S, h, a, b)
                                    fails += 1
                                    return 1
    print(f"checked_sets={checked_sets} checked_equal_sum_ordered_pairs={checked_pairs} fails={fails}")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
