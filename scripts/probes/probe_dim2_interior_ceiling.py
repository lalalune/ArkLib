#!/usr/bin/env python3
"""Probe for the r = 3 (dimension-two) slice interior ceiling (#371 dimension ladder).

Code: evalCode g n 1 = degree-<=1 (affine) words on the smooth domain x_i = g^i,
n = 2^mu, orderOf g = n.  KKH26 ceiling radius for r = 3: delta = 1 - 3/2^mu.
Below the ceiling the witness-set threshold is |S| >= 4.

CLAIM under test (the triple-ownership count, Lean: dimTwo_badScalars_card_mul_twelve_le):
  for EVERY stack (u0, u1) and every prime p with an order-n element g,
    #bad scalars at threshold 4  <=  n(n-1)(n-2)/12     ( = 28 at n = 8 ).

Also checked:
  * three independent badness criteria agree byte-exactly per (stack, gamma):
      (E)  exhaustive mcaEvent over all S with |S| >= t (the Lean definition);
      (D)  derived criterion: exists S, |S| >= t, u_gamma|S affine and u1|S NOT affine
           (the step-1 reduction: no-joint-pair <=> u1 non-affine given the level constraint);
      (F)  fast criterion: exists pair-generated affine w whose full agreement set A_w
           has |A_w| >= t and u1|A_w not affine.
  * the band is real: the KKH26 stack (u0, u1) = (x^3, x^2) at threshold 3 (the ceiling
    radius) has bad count >= 2^3 * C(4,3) = 32 > 28.

Run: python3 scripts/probes/probe_dim2_interior_ceiling.py
"""

import itertools
import random

random.seed(371)

P = 257
G = 4  # order 8 mod 257 (4^4 = 256 = -1)
N = 8
X = [pow(G, i, P) for i in range(N)]
assert len(set(X)) == N and pow(G, N, P) == 1 and pow(G, N // 2, P) == P - 1

BOUND = N * (N - 1) * (N - 2) // 12  # 28
CEILING_COUNT = 8 * 4  # 2^3 * C(4,3) = 32


def is_affine(idxs, y):
    """points (X[i], y[i]) for i in idxs all on one affine line (distinct X's)."""
    if len(idxs) <= 2:
        return True
    a, b = idxs[0], idxs[1]
    for c in idxs[2:]:
        d = ((X[b] - X[a]) * (y[c] - y[a]) - (X[c] - X[a]) * (y[b] - y[a])) % P
        if d != 0:
            return False
    return True


def bad_exhaustive(u0, u1, gamma, t):
    """(E) literal mcaEvent: exists S, |S| >= t, u_g|S affine, and NOT (u0|S affine and u1|S affine)."""
    ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
    for s in range(t, N + 1):
        for S in itertools.combinations(range(N), s):
            if is_affine(S, ug) and not (is_affine(S, u0) and is_affine(S, u1)):
                return True
    return False


def bad_derived(u0, u1, gamma, t):
    """(D) exists S, |S| >= t, u_g|S affine, u1|S not affine."""
    ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
    for s in range(t, N + 1):
        for S in itertools.combinations(range(N), s):
            if is_affine(S, ug) and not is_affine(S, u1):
                return True
    return False


def bad_fast(u0, u1, gamma, t):
    """(F) exists pair-generated affine w with |A_w| >= t and u1|A_w not affine."""
    ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
    for a, b in itertools.combinations(range(N), 2):
        inv = pow(X[b] - X[a], P - 2, P)
        c1 = (ug[b] - ug[a]) * inv % P
        c0 = (ug[a] - c1 * X[a]) % P
        A = [i for i in range(N) if (c0 + c1 * X[i] - ug[i]) % P == 0]
        if len(A) >= t and not is_affine(A, u1):
            return True
    return False


def count_bad(u0, u1, t, check_all=False):
    cnt = 0
    for g in range(P):
        f = bad_fast(u0, u1, g, t)
        if check_all:
            e = bad_exhaustive(u0, u1, g, t)
            d = bad_derived(u0, u1, g, t)
            assert e == d == f, (u0, u1, g, e, d, f)
        if f:
            cnt += 1
    return cnt


def rand_stack():
    return ([random.randrange(P) for _ in range(N)],
            [random.randrange(P) for _ in range(N)])


def main():
    maxbad, argmax = 0, None

    # 1. KKH26 stack at the ceiling radius (threshold 3): the band's right edge is real.
    kk_u0 = [pow(x, 3, P) for x in X]
    kk_u1 = [pow(x, 2, P) for x in X]
    ceil_cnt = count_bad(kk_u0, kk_u1, 3, check_all=True)
    print(f"KKH26 stack (x^3, x^2), threshold 3 (ceiling): bad = {ceil_cnt} "
          f"(in-tree lower bound {CEILING_COUNT})")
    assert ceil_cnt >= CEILING_COUNT, "ceiling bad count below the in-tree bound!"

    # 2. Structured stacks at threshold 4 (below the ceiling), full 3-checker agreement.
    structured = [(kk_u0, kk_u1), (kk_u1, kk_u0)]
    for e0 in range(4):
        for e1 in range(4):
            structured.append(([pow(x, e0, P) for x in X], [pow(x, e1, P) for x in X]))
    for u0, u1 in structured:
        c = count_bad(u0, u1, 4, check_all=True)
        if c > maxbad:
            maxbad, argmax = c, (u0, u1)
    print(f"structured stacks ({len(structured)}), threshold 4: max bad = {maxbad}")

    # 3. Random stacks (3-checker agreement on a slice).
    for k in range(120):
        u0, u1 = rand_stack()
        c = count_bad(u0, u1, 4, check_all=(k < 12))
        if c > maxbad:
            maxbad, argmax = c, (u0, u1)
    print(f"after 120 random stacks: max bad = {maxbad}")

    # 4. Hill-climb from the best seen.
    cur = argmax if argmax else rand_stack()
    cur_c = maxbad
    for _ in range(900):
        u0, u1 = [list(cur[0]), list(cur[1])]
        for _ in range(random.randrange(1, 3)):
            which = random.randrange(2)
            (u0 if which == 0 else u1)[random.randrange(N)] = random.randrange(P)
        c = count_bad(u0, u1, 4)
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    maxbad = max(maxbad, cur_c)
    print(f"after hill-climb: max bad = {maxbad}")

    print(f"\nclaimed Lean bound: n(n-1)(n-2)/12 = {BOUND}")
    assert maxbad <= BOUND, f"COUNTEREXAMPLE to the triple-ownership bound: {maxbad} > {BOUND}"
    print(f"band check at n=8: {BOUND} < {CEILING_COUNT} -> band [28/p, 32/p) NONEMPTY")
    assert BOUND < CEILING_COUNT
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
