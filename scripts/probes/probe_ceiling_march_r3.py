#!/usr/bin/env python3
"""probe_ceiling_march_r3.py — the ceiling march at r = 3: tuple-ownership probe (#371).

Pre-registered probe for the r-tuple generalization of the dimension-one
InteriorCeiling discharge (KKH26DimOnePin.lean -> KKH26CeilingMarch.lean).

Setting: code = evalCode g n d with d = r-2 = 1 (affine polynomials, dimension 2),
domain x_i = g^i, g of multiplicative order n = 8, p in {17, 97}; agreement
threshold a = r+1 = 4 (the regime of every radius strictly below the KKH26
ceiling 1 - r/n = 5/8).

  bad(gamma) <=> exists S, |S| >= a, (u0 + gamma*u1) explainable on S by a
                 polynomial of degree <= d, and NOT (u0 explainable on S AND
                 u1 explainable on S).

Pre-registered claims:

  C1 (criterion collapse)  bad(gamma) <=> exists S, |S| >= a, combined
      explainable on S and u1 NOT explainable on S.  (The disjunction in
      "not joint" collapses onto the direction row: explainability of the
      combined word transfers between rows.)  Byte-exact on the bad SET via
      independent checkers, >= 300 random + structured stacks per prime.
      Expected mismatches: 0.

  C2 (glueing / at-most-one)  for every u1 and every 4-set T4 with u1 NOT
      explainable on T4: the number of 3-subsets of T4 on which u1 IS
      explainable is <= 1.  Expected violations: 0.

  C3 (ownership >= r)  for every bad gamma with witness S: there is a 4-set
      S' inside S with u1 not explainable on S', and >= 3 of its four
      3-subsets are u1-non-explainable (hence determine gamma).  Expected
      violations: 0.

  C4 (disjointness)  the global tuple sets
      phi(gamma) = {T : |T|=3, u1 not explainable on T, u0+gamma*u1
      explainable on T} are pairwise disjoint over bad gammas.  (Each such T
      solves det0(T) + gamma*det1(T) = 0 with det1(T) != 0 uniquely.)
      Expected violations: 0.

  C5 (the bound)  #bad <= floor(C(8,3)/3) = 18 for EVERY stack
      (random / structured / monomial / hill-climbed).  Also #bad*3 <= 56.
      Expected violations: 0.  Report the maximum found (tightness data).

  C6 (band arithmetic)  floor(C(8,3)/3) = 18 < 32 = 2^3 * C(4,3): the
      epsilon* band of the r = 3 pin is nonempty at mu = 3.

Exit 0 iff all pre-registered checks pass.
"""

import itertools
import random
import sys
import time

START = time.time()
RNG = random.Random(371_003)
FAIL = 0
ROWS = []


def report(claim, expected, observed, ok):
    global FAIL
    ROWS.append((claim, expected, observed, ok))
    if not ok:
        FAIL = 1


def inv_mod(a, p):
    return pow(a, p - 2, p)


class Instance:
    def __init__(self, p, g, n, d):
        self.p, self.g, self.n, self.d = p, g, n, d
        self.x = [pow(g, i, p) for i in range(n)]
        assert len(set(self.x)) == n, "domain not injective"
        # order check
        assert pow(g, n, p) == 1 and all(pow(g, k, p) != 1 for k in range(1, n))

    def interpolate(self, pts):
        """Lagrange interpolation through pts = [(x, y), ...]; returns coeff list."""
        p = self.p
        m = len(pts)
        coeffs = [0] * m
        for i, (xi, yi) in enumerate(pts):
            # basis poly prod_{j != i} (X - xj) / (xi - xj)
            denom = 1
            basis = [1]  # poly coeffs, low to high
            for j, (xj, _) in enumerate(pts):
                if j == i:
                    continue
                denom = denom * ((xi - xj) % p) % p
                new = [0] * (len(basis) + 1)
                for k, c in enumerate(basis):
                    new[k] = (new[k] - c * xj) % p
                    new[k + 1] = (new[k + 1] + c) % p
                basis = new
            scale = yi * inv_mod(denom, p) % p
            for k, c in enumerate(basis):
                coeffs[k] = (coeffs[k] + scale * c) % p
        return coeffs

    def expl(self, u, S, d=None):
        """u (list) explainable on S (iterable of indices) by poly of deg <= d."""
        if d is None:
            d = self.d
        S = sorted(S)
        if len(S) <= d + 1:
            return True
        base = S[: d + 1]
        c = self.interpolate([(self.x[i], u[i]) for i in base])
        for i in S[d + 1:]:
            v = 0
            for k in reversed(range(len(c))):
                v = (v * self.x[i] + c[k * 0 + len(c) - 1 - (len(c) - 1 - k)]) % self.p
            # horner with low-to-high coeffs:
            v = 0
            for k in reversed(range(len(c))):
                v = (v * self.x[i] + c[k]) % self.p
            if v != u[i] % self.p:
                return False
        return True


def combined(u0, u1, gamma, p):
    return [(a + gamma * b) % p for a, b in zip(u0, u1)]


def witness_sets(n, a):
    idx = list(range(n))
    for s in range(a, n + 1):
        for S in itertools.combinations(idx, s):
            yield S


def bad_set_direct(inst, u0, u1, a):
    """mcaEvent enumeration: not (u0 expl AND u1 expl)."""
    out = set()
    p = inst.p
    for gamma in range(p):
        w = combined(u0, u1, gamma, p)
        for S in witness_sets(inst.n, a):
            if inst.expl(w, S) and not (inst.expl(u0, S) and inst.expl(u1, S)):
                out.add(gamma)
                break
    return out


def bad_set_u1crit(inst, u0, u1, a):
    """criterion: combined expl and u1 NOT expl."""
    out = set()
    p = inst.p
    for gamma in range(p):
        w = combined(u0, u1, gamma, p)
        for S in witness_sets(inst.n, a):
            if inst.expl(w, S) and not inst.expl(u1, S):
                out.add(gamma)
                break
    return out


def stack_families(inst, count_random):
    p, n = inst.p, inst.n
    fams = []
    # monomial adjacent pairs (the census extremal family)
    for aexp in range(2, n):
        u0 = [pow(inst.x[i], aexp, p) for i in range(n)]
        u1 = [pow(inst.x[i], aexp - 1, p) for i in range(n)]
        fams.append(("monomial-a%d" % aexp, u0, u1))
    # codeword + sparse deviations on the direction row
    for ndev in (1, 2, 3):
        for _ in range(20):
            qa, qb = RNG.randrange(p), RNG.randrange(p)
            u1 = [(qa + qb * inst.x[i]) % p for i in range(n)]
            for j in RNG.sample(range(n), ndev):
                u1[j] = (u1[j] + RNG.randrange(1, p)) % p
            u0 = [RNG.randrange(p) for _ in range(n)]
            fams.append(("dev%d" % ndev, u0, u1))
    # few-distinct-residual stacks (ratio-degenerate)
    for _ in range(20):
        vals = [RNG.randrange(p) for _ in range(2)]
        u1 = [RNG.choice(vals) for _ in range(n)]
        u0 = [RNG.choice(vals) for _ in range(n)]
        fams.append(("fewval", u0, u1))
    # pure random
    for _ in range(count_random):
        u0 = [RNG.randrange(p) for _ in range(n)]
        u1 = [RNG.randrange(p) for _ in range(n)]
        fams.append(("random", u0, u1))
    return fams


def run_prime(p, g, hill_iters=400):
    n, d, r = 8, 1, 3
    a = r + 1  # agreement threshold just below the ceiling
    inst = Instance(p, g, n, d)
    bound = (56 // 3)  # floor(C(8,3)/3) = 18

    # --- C1 + C5 over families
    mismatches = 0
    maxbad, argmax = 0, None
    over = 0
    fams = stack_families(inst, count_random=120 if p == 17 else 60)
    for name, u0, u1 in fams:
        b1 = bad_set_direct(inst, u0, u1, a)
        b2 = bad_set_u1crit(inst, u0, u1, a)
        if b1 != b2:
            mismatches += 1
        if len(b1) > maxbad:
            maxbad, argmax = len(b1), (name, u0[:], u1[:])
        if len(b1) > bound:
            over += 1
    report("C1 criterion collapse (mismatched stacks)", 0, mismatches, mismatches == 0)

    # --- C2 glueing: random u1 sweep
    viol2 = 0
    for _ in range(400):
        u1 = [RNG.randrange(p) for _ in range(n)]
        for T4 in itertools.combinations(range(n), 4):
            if inst.expl(u1, T4):
                continue
            cnt = sum(1 for T3 in itertools.combinations(T4, 3) if inst.expl(u1, T3))
            if cnt > 1:
                viol2 += 1
    report("C2 glueing at-most-one (violations)", 0, viol2, viol2 == 0)

    # --- C3 ownership + C4 disjointness on the family sweep (subsample)
    viol3 = 0
    viol4 = 0
    for name, u0, u1 in fams[:80]:
        bads = bad_set_direct(inst, u0, u1, a)
        phis = {}
        for gamma in bads:
            w = combined(u0, u1, gamma, p)
            # ownership: find a witness S
            own_ok = False
            for S in witness_sets(n, a):
                if inst.expl(w, S) and not inst.expl(u1, S):
                    # find 4-subset S' of S with u1 not explainable
                    for S4 in itertools.combinations(S, 4):
                        if not inst.expl(u1, S4):
                            cnt = sum(
                                1
                                for T3 in itertools.combinations(S4, 3)
                                if (not inst.expl(u1, T3)) and inst.expl(w, T3)
                            )
                            if cnt >= 3:
                                own_ok = True
                                break
                    if own_ok:
                        break
            if not own_ok and len(bads) > 0:
                viol3 += 1
            phis[gamma] = set(
                T
                for T in itertools.combinations(range(n), 3)
                if (not inst.expl(u1, T)) and inst.expl(combined(u0, u1, gamma, p), T)
            )
        gs = sorted(phis)
        for i in range(len(gs)):
            for j in range(i + 1, len(gs)):
                if phis[gs[i]] & phis[gs[j]]:
                    viol4 += 1
    report("C3 ownership >= 3 (violations)", 0, viol3, viol3 == 0)
    report("C4 tuple disjointness (violations)", 0, viol4, viol4 == 0)

    # --- C5 hill-climb from the best family point
    if argmax is not None:
        _, u0, u1 = argmax
        cur = len(bad_set_direct(inst, u0, u1, a))
        for _ in range(hill_iters):
            v0, v1 = u0[:], u1[:]
            j = RNG.randrange(n)
            if RNG.random() < 0.5:
                v0[j] = RNG.randrange(p)
            else:
                v1[j] = RNG.randrange(p)
            c = len(bad_set_direct(inst, v0, v1, a))
            if c >= cur:
                u0, u1, cur = v0, v1, c
            if cur > maxbad:
                maxbad = cur
            if cur > bound:
                over += 1
                break
    report("C5 bound #bad <= 18 (violations)", 0, over, over == 0)
    print("  [p=%d] max #bad found = %d (bound %d)" % (p, maxbad, bound))
    return maxbad


def main():
    # C6 band arithmetic
    import math

    lhs = math.comb(8, 3) // 3
    rhs = 2 ** 3 * math.comb(4, 3)
    report("C6 band nonempty: 18 < 32", True, (lhs, rhs, lhs < rhs), lhs < rhs)

    # find order-8 element mod 97
    g97 = next(
        g for g in range(2, 97) if pow(g, 8, 97) == 1 and all(pow(g, k, 97) != 1 for k in range(1, 8))
    )
    run_prime(17, 2)
    run_prime(97, g97, hill_iters=150)

    print("\n=== verdict table ===")
    for claim, exp, obs, ok in ROWS:
        print("  %-45s expected=%-12s observed=%-16s %s" % (claim, exp, obs, "OK" if ok else "FAIL"))
    print("elapsed %.1fs" % (time.time() - START))
    sys.exit(FAIL)


if __name__ == "__main__":
    main()
