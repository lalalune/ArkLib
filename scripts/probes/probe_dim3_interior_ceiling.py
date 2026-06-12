#!/usr/bin/env python3
"""Probe for the r = 4 (dimension-three) slice interior ceiling (#371 dimension ladder).

Code: evalCode g n 2 = degree-<=2 (quadratic) words on the smooth domain x_i = g^i,
n = 2^mu = 16 (mu = 4), orderOf g = n.  KKH26 ceiling radius for r = 4: delta = 1 - 4/16.
Below the ceiling the witness-set threshold is |S| >= 5 = (d+3) with d = r-2 = 2.

CLAIM under test (the general subset-ownership count, Lean:
dimGeneral_badScalars_card_mul_two_le at d = 2):
  for EVERY stack (u0, u1) and every prime p with an order-16 element g,
    #bad scalars at threshold 5  <=  C(16, 4)/2 = 910.

The K(r) = 2*r! ladder law, restated set-theoretically: each bad scalar owns >= 2
UNORDERED bad (d+2)-subsets (equivalently >= 2*r! = 48 ordered tuples), the owned sets
are disjoint across scalars, and only C(n, d+2) subsets exist; n^{(r)}/(2*r!) = C(n,r)/2.

Two lanes:
  * SMALL lane p = 97 (order-16 element g = 8): three independent badness criteria agree
    byte-exactly per (stack, gamma) --
      (E)  exhaustive mcaEvent over all S with |S| >= t (the Lean definition);
      (D)  derived: exists S, |S| >= t, u_gamma|S quadratic-fit and u1|S NOT
           (the step-1 reduction: no-joint-pair <=> u1 non-fit given the line constraint);
      (F)  fast: exists triple-generated quadratic w with |A_w| >= t, u1|A_w not fit --
    plus structured/random/hill-climb max-bad <= 910 and the ownership >= 2 law.
  * BIG lane p = 4294967377 = 2^32 + 81 (the instance prime: smallest prime > 2^32 with
    p = 1 mod 16; hp: 16^8 = 2^32 < p), g = 526957872 of order 16: the KKH26 stack
    (x^4, x^3) at the ceiling radius has EXACTLY N(4,4) = 1233 bad scalars (the
    TwoPowerSubsetSumSpectrum law N(mu,r) = sum_{a == r mod 2, (r-a)/2 <= h-a} 2^a C(h,a),
    h = 8: 2^4 C(8,4) + 2^2 C(8,2) + C(8,0) = 1120 + 112 + 1), >= the in-tree term 1120
    > 910; bad scalars enumerated through the 4-point-defect candidate map (each bad
    scalar at threshold >= 4 is determined by an owned 4-subset with nonzero u1-defect,
    so the candidate sweep is exhaustive and p-independent in cost).
  * The big lane is also run at p = 12289 (16 | 12288) WITHOUT assertion: the spectrum
    turns out to SURVIVE there too (1233), documenting that the in-tree size hypothesis
    hp: 2^32 < p is sufficient-not-necessary -- but the Lean instance still consumes
    kkh26_epsMCA_lower_bound, whose hypothesis at mu = 4 is hp, hence the big prime.

Run: python3 scripts/probes/probe_dim3_interior_ceiling.py
"""

import itertools
import random
from math import comb

random.seed(371)

N = 16
D = 2                                  # code degree bound (r = 4, m = 1)
T_BELOW = D + 3                        # = 5, threshold strictly below the ceiling
T_CEIL = 4                             # = r*m, threshold AT the ceiling radius
BOUND = comb(N, D + 2) // 2            # C(16,4)/2 = 910
CEILING_TERM = 2 ** 4 * comb(8, 4)     # 1120 (in-tree lower-bound term)
SPECTRUM = sum(2 ** a * comb(8, a) for a in (0, 2, 4))  # N(4,4) = 1233


class Domain:
    def __init__(self, p, g):
        self.P, self.G = p, g
        self.X = [pow(g, i, p) for i in range(N)]
        assert len(set(self.X)) == N and pow(g, N, p) == 1
        assert pow(g, N // 2, p) == p - 1

    def quad_through(self, i, j, k, y):
        """coefficients (c0, c1, c2) of the quadratic through (X[t], y[t]), t in {i,j,k}."""
        P, X = self.P, self.X
        xi, xj, xk = X[i], X[j], X[k]
        li = y[i] * pow((xi - xj) * (xi - xk), P - 2, P) % P
        lj = y[j] * pow((xj - xi) * (xj - xk), P - 2, P) % P
        lk = y[k] * pow((xk - xi) * (xk - xj), P - 2, P) % P
        c2 = (li + lj + lk) % P
        c1 = (-(li * (xj + xk) + lj * (xi + xk) + lk * (xi + xj))) % P
        c0 = (li * xj * xk + lj * xi * xk + lk * xi * xj) % P
        return c0, c1, c2

    def fits_quad(self, idxs, y):
        """y restricted to idxs is a deg-<=2 polynomial evaluation (distinct X's)."""
        idxs = list(idxs)
        if len(idxs) <= 3:
            return True
        P, X = self.P, self.X
        c0, c1, c2 = self.quad_through(idxs[0], idxs[1], idxs[2], y)
        return all((c0 + c1 * X[t] + c2 * X[t] * X[t] - y[t]) % P == 0 for t in idxs[3:])

    def defect(self, R, y):
        """the 4-point degree-2 interpolation defect: y[l] - (quad through i,j,k)(x_l).
        Linear in y; zero iff y fits a quadratic on R = (i, j, k, l)."""
        i, j, k, l = R
        P, X = self.P, self.X
        c0, c1, c2 = self.quad_through(i, j, k, y)
        return (y[l] - (c0 + c1 * X[l] + c2 * X[l] * X[l])) % P

    def bad_fast(self, u0, u1, gamma, t):
        """(F) exists triple-generated quadratic w with |A_w| >= t and u1|A_w not fit."""
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for a, b, c in itertools.combinations(range(N), 3):
            c0, c1, c2 = self.quad_through(a, b, c, ug)
            A = [i for i in range(N)
                 if (c0 + c1 * X[i] + c2 * X[i] * X[i] - ug[i]) % P == 0]
            if len(A) >= t and not self.fits_quad(A, u1):
                return True
        return False

    def bad_exhaustive(self, u0, u1, gamma, t):
        """(E) literal mcaEvent: exists S, |S| >= t, u_g|S fit, NOT (u0 and u1 fit on S)."""
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for s in range(t, N + 1):
            for S in itertools.combinations(range(N), s):
                if self.fits_quad(S, ug) and not (self.fits_quad(S, u0)
                                                  and self.fits_quad(S, u1)):
                    return True
        return False

    def bad_derived(self, u0, u1, gamma, t):
        """(D) exists S, |S| >= t, u_g|S fit, u1|S not fit."""
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for s in range(t, N + 1):
            for S in itertools.combinations(range(N), s):
                if self.fits_quad(S, ug) and not self.fits_quad(S, u1):
                    return True
        return False

    def bad_candidates(self, u0, u1):
        """every bad scalar (at threshold >= 4) satisfies defect_R(u0) + g*defect_R(u1) = 0
        on some 4-subset R with defect_R(u1) != 0, so this candidate set is exhaustive."""
        P = self.P
        cands = set()
        for R in itertools.combinations(range(N), 4):
            d1 = self.defect(R, u1)
            if d1 != 0:
                d0 = self.defect(R, u0)
                cands.add((-d0) * pow(d1, P - 2, P) % P)
        return cands

    def count_bad_via_candidates(self, u0, u1, t):
        return sum(1 for g in self.bad_candidates(u0, u1)
                   if self.bad_fast(u0, u1, g, t))

    def count_bad_all_gammas(self, u0, u1, t, check_all=False):
        cnt = 0
        for g in range(self.P):
            f = self.bad_fast(u0, u1, g, t)
            if check_all:
                e = self.bad_exhaustive(u0, u1, g, t)
                d = self.bad_derived(u0, u1, g, t)
                assert e == d == f, (u0, u1, g, e, d, f)
            if f:
                cnt += 1
        return cnt

    def owned_bad_sets(self, u0, u1, gamma, t):
        """unordered (D+2)-subsets R inside some witness with u1|R not quadratic-fit
        (the ownership objects of the Lean proof)."""
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        owned = set()
        for a, b, c in itertools.combinations(range(N), 3):
            c0, c1, c2 = self.quad_through(a, b, c, ug)
            A = [i for i in range(N)
                 if (c0 + c1 * X[i] + c2 * X[i] * X[i] - ug[i]) % P == 0]
            if len(A) >= t and not self.fits_quad(A, u1):
                for R in itertools.combinations(A, D + 2):
                    if not self.fits_quad(R, u1):
                        owned.add(R)
        return owned


def small_lane():
    dom = Domain(97, 8)
    P = dom.P
    print(f"== SMALL lane p = {P}, g = {dom.G} ==")
    kk_u0 = [pow(x, 4, P) for x in dom.X]
    kk_u1 = [pow(x, 3, P) for x in dom.X]
    maxbad, argmax = 0, None

    structured = [(kk_u0, kk_u1), (kk_u1, kk_u0)]
    for e0 in range(5):
        for e1 in range(5):
            structured.append(([pow(x, e0, P) for x in dom.X],
                               [pow(x, e1, P) for x in dom.X]))
    for idx, (u0, u1) in enumerate(structured):
        c = dom.count_bad_all_gammas(u0, u1, T_BELOW, check_all=(idx < 2))
        if c > maxbad:
            maxbad, argmax = c, (u0, u1)
    print(f"structured stacks ({len(structured)}), threshold 5: max bad = {maxbad} "
          f"(3-checker byte-exact on the first 2 stacks x all {P} gammas)")

    def rand_stack():
        return ([random.randrange(P) for _ in range(N)],
                [random.randrange(P) for _ in range(N)])

    for k in range(40):
        u0, u1 = rand_stack()
        c = dom.count_bad_all_gammas(u0, u1, T_BELOW, check_all=(k < 2))
        if c > maxbad:
            maxbad, argmax = c, (u0, u1)
    print(f"after 40 random stacks (3-checker on first 2): max bad = {maxbad}")

    cur = argmax if argmax else rand_stack()
    cur_c = maxbad
    for _ in range(200):
        u0, u1 = [list(cur[0]), list(cur[1])]
        for _ in range(random.randrange(1, 3)):
            which = random.randrange(2)
            (u0 if which == 0 else u1)[random.randrange(N)] = random.randrange(P)
        c = dom.count_bad_via_candidates(u0, u1, T_BELOW)
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    maxbad = max(maxbad, cur_c)
    print(f"after hill-climb: max bad = {maxbad}")
    assert maxbad <= BOUND, f"COUNTEREXAMPLE to the subset-ownership bound: {maxbad} > {BOUND}"

    min_owned = None
    for u0, u1 in [structured[0], structured[1]] + [rand_stack() for _ in range(3)]:
        for g in dom.bad_candidates(u0, u1):
            if dom.bad_fast(u0, u1, g, T_BELOW):
                k = len(dom.owned_bad_sets(u0, u1, g, T_BELOW))
                min_owned = k if min_owned is None else min(min_owned, k)
    print(f"min unordered bad-4-set ownership over sampled bad scalars: {min_owned} "
          f"(law: >= 2, i.e. >= 2*4! = 48 ordered)")
    if min_owned is not None:
        assert min_owned >= 2, "ownership law K(r) = 2*r! FAILS at r = 4!"
    print(f"small lane OK: max bad {maxbad} <= C(16,4)/2 = {BOUND}\n")


def big_lane(p, g, assert_spectrum):
    dom = Domain(p, g)
    print(f"== BIG lane p = {p}, g = {g} ==")
    kk_u0 = [pow(x, 4, p) for x in dom.X]
    kk_u1 = [pow(x, 3, p) for x in dom.X]
    ceil_cnt = dom.count_bad_via_candidates(kk_u0, kk_u1, T_CEIL)
    below_cnt = dom.count_bad_via_candidates(kk_u0, kk_u1, T_BELOW)
    print(f"KKH26 stack (x^4, x^3): ceiling-threshold-4 bad = {ceil_cnt} "
          f"(spectrum law N(4,4) = {SPECTRUM}, in-tree term {CEILING_TERM}); "
          f"below-threshold-5 bad = {below_cnt} (bound {BOUND})")
    if assert_spectrum:
        assert ceil_cnt == SPECTRUM, f"spectrum law violated: {ceil_cnt} != {SPECTRUM}"
        assert ceil_cnt >= CEILING_TERM
        assert below_cnt <= BOUND
        print(f"big lane OK: spectrum EXACT ({SPECTRUM}), band [910/p, 1120/p) real\n")
    else:
        print("(no assertion: documents that the in-tree hp is sufficient-not-necessary "
              "-- the spectrum survives even at p = 12289, but the Lean route consumes "
              "kkh26_epsMCA_lower_bound whose hypothesis is hp: 2^32 < p at mu = 4)\n")


def main():
    small_lane()
    big_lane(12289, 4134, False)  # 4134 = 11^(12288/16) has order 16 mod 12289
    big_lane(4294967377, 526957872, True)
    print(f"band check at n=16: {BOUND} < {CEILING_TERM} -> band [910/p, 1120/p) NONEMPTY")
    assert BOUND < CEILING_TERM
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
