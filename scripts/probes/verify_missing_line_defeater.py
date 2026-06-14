#!/usr/bin/env python3
"""verify_missing_line_defeater.py — independent verification of the S2(b) defeaters.

Written from the definitions with tuple semantics (no bitmask encodings, no
canonicalization, no shared code with the search probes), to cross-validate the
two MissingLine defeaters found by probe_missing_line_heavy_fast.py:

  * F2, n=4, k=1 (repetition code), delta=1/2 (|T|>=2):
        stack rows ((1,2),(2,5)) -> H expected 3 > q = 2
  * F3, n=4, k=1, delta=1/2:
        stack rows ((1,3),(9,13)) -> H expected 4 > q = 3

Also reports, per bad seed, the full family V_omega of obstruction values with
subspace structure, and whether the K-values are genuine subspaces — plus the
interleaving-exactness side-question data: the per-seed witness lists.
"""

import itertools
import sys


def decode(code, P, N):
    out = []
    for _ in range(N):
        out.append(code % P)
        code //= P
    return tuple(out)


def verify(P, N, rowcodes, expect_H):
    print(f"\n=== F_{P}, n={N}, k=1, |T|>=2, stack rows {rowcodes} ===")
    cws = [tuple([c] * N) for c in range(P)]
    (x0c, y0c), (x1c, y1c) = rowcodes
    x0, y0 = decode(x0c, P, N), decode(y0c, P, N)
    x1, y1 = decode(x1c, P, N), decode(y1c, P, N)
    print(f"row0: x0={x0} y0={y0}\nrow1: x1={x1} y1={y1}")

    def add(u, v, a=1, b=1):
        return tuple((a * ui + b * vi) % P for ui, vi in zip(u, v))

    def explainable(w, T):
        return any(all(w[i] == c[i] for i in T) for c in cws)

    masks = [T for r in range(2, N + 1) for T in itertools.combinations(range(N), r)]
    lambdas = list(itertools.product(range(P), repeat=2))
    seeds = list(itertools.product(range(P), repeat=2))

    def K_of(T):
        return frozenset(l for l in lambdas
                         if explainable(add(x0, y0, l[0], l[1]), T)
                         and explainable(add(x1, y1, l[0], l[1]), T))

    def is_subspace(K):
        if (0, 0) not in K:
            return False
        for u in K:
            for v in K:
                for a in range(P):
                    for b in range(P):
                        if tuple((a * ui + b * vi) % P for ui, vi in zip(u, v)) \
                                not in K:
                            return False
        return True

    fams = {}
    for (a, b) in seeds:
        c0 = add(x0, x1, a, b)
        c1 = add(y0, y1, a, b)
        V = set()
        for T in masks:
            joint = all(explainable(w, T) for w in (x0, y0, x1, y1))
            if joint:
                continue
            if explainable(c0, T) and explainable(c1, T):
                K = K_of(T)
                assert is_subspace(K), (T, K)
                full = frozenset(lambdas)
                assert K != full, "non-joint mask with full obstruction!"
                V.add(K)
        if V:
            fams[(a, b)] = V
    print(f"bad seeds: {sorted(fams)}")
    for s, V in sorted(fams.items()):
        print(f"  seed {s}: {len(V)} obstruction value(s): "
              f"{[sorted(K) for K in sorted(V, key=sorted)]}")
    uni = sorted({K for V in fams.values() for K in V}, key=sorted)
    print(f"distinct obstruction values: {len(uni)}")
    H = len(uni)
    for size in range(1, len(uni) + 1):
        if any(all(set(combo) & V for V in fams.values())
               for combo in itertools.combinations(uni, size)):
            H = size
            break
    print(f"min hitting set H = {H} (expected {expect_H}); q = {P}")
    verdict = "DEFEATER CONFIRMED" if H > P else "no defeat"
    ok = "MATCH" if H == expect_H else "MISMATCH"
    print(f"{verdict}; cross-engine {ok}")
    return H == expect_H and H > P


def main():
    ok1 = verify(2, 4, ((1, 2), (2, 5)), 3)
    ok2 = verify(3, 4, ((1, 3), (9, 13)), 4)
    print(f"\noverall: {'BOTH DEFEATERS CONFIRMED' if ok1 and ok2 else 'FAILURE'}")
    return 0 if (ok1 and ok2) else 1


if __name__ == "__main__":
    sys.exit(main())
