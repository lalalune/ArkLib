#!/usr/bin/env python3
"""Probe the LEVEL-1 RUNG PIN good side (#371 round 7, Level1RungPin.lean).

THE QUESTION.  At the first biting instance (n = 16, d = 2, the dim-3 code on the
16-point smooth domain; level-1 rung radius 5/8, provable bad count K_1 = 32, exact
N_1 = 40), pinning deltaStar = 5/8 on a band [b/p, 32/p) needs the GOOD side

    W_7  :=  max over stacks (u0, u1) of #bad scalars at threshold 7
             (threshold 7 <=> radius delta in [9/16, 5/8); threshold 8 <=> [1/2, 9/16))

to satisfy W_7 <= b <= 31.  The in-tree ownership engine gives 208 at threshold 7
(pairs law, w0 = 6); the ABSOLUTE cap of per-witness (d+2)-subset counting is
C(16,4)/C(7,4) = 52 > 31 -- the scheme provably cannot certify the band, so the good
side must enter Lean as a named obligation.  This probe measures the TRUTH.

CORRECTION OF THE OLD S6 (probe_subceiling_envelope.py).  The old hill-climb pool
contained monomial exponents 0..4 only and missed the LEVEL-2 stack (X^8, X^4), whose
witnesses are 8-point fibers (>= 7): its 5 = N(2,2) bad scalars SURVIVE at threshold 7.
So the old "observed worst stack = 1" was a search artifact; the truth is >= 5.

THE DISCOVERY (found by P2 below; formalized as antipodal_pencil_epsMCA_lower_bound in
Level1RungPin.lean).  The monomial sweep's maximizer is the ANTIPODAL PENCIL
(X^8, X^9) = (X^h, X^{h+1}), h = n/2: since x^h = +-1 on the domain, the line
x^h(1+gamma*x) IS the degree-1 word +-(1+gamma*X) on a full antipodal half-coset plus
the single rotating cross-coset point x0 = -1/gamma, while the direction x^h*x = +-x
deviates there.  All n = 16 scalars of the inversion orbit -1/<g> are bad at radius
1 - (h+1)/n = 7/16 < 1/2 = the deepest staircase rung, for EVERY degree 1 <= d <= h-1.
Consequences: the level-j staircase is NOT the complete envelope; the d = 4 level-1
rung (K_1 = 16) is REFUTED outright (16 bad at 7/16 on its whole band); the d = 2
level-1 pin band is trapped to [16/p, 32/p).

WHAT THIS PROBE CHECKS:
  P1  the floor: the level-2 stack (X^8, X^4) has exactly 5 bad scalars at thresholds
      7 AND 8 (its fibers have 8 points) -- at p = 97, 12289, 17.
  P2  full monomial sweep: max bad over ALL (e0, e1) in [0,16)^2 at threshold 7
      (p = 97 and p = 17 exhaustive; p = 12289 on the structured shortlist).
  P3  adversarial: deviations / code-shifts / scalings of the level-2 stack, splices
      of level-1 and level-2 directions, random stacks, and a greedy+random hill-climb
      (single-point edits, exhaustive over values at p = 17) seeded at the known
      maximizer -- can anything beat 5?
  P4  the second instance (n = 16, d = 4, rate 5/16; level-1 radius 1/2, K_1 = 16,
      threshold just below = 9): same sweep at p = 97 -- floor stack (X^12, X^8)
      (level-2 rung r'_2 = 3, 12-point fibers) and monomial max at threshold 9.
  P5  budget table: W_7 (observed) vs the floor N_2 = 5, the provable K_1 = 32, the
      exact N_1 = 40, the engine value 208, and the scheme cap 52.

Soundness of the fast counter: every bad scalar at threshold t >= d+3 owns, inside its
witness, >= ceil(C(t, d+1)/(d+2)) >= 9 (t = 7, d = 2) distinct unfit (d+2)-subsets R,
each pinning gamma = -defect_R(u0)/defect_R(u1) (the proven sharpened ownership law,
OwnershipCensusSharpened.lean).  So candidates with defect-ratio multiplicity >= 9 are
exhaustive at threshold 7; we use the safe generic floor ceil(C(t,d+1)/(d+2)) at each
(t, d) and verify each survivor with the complete bad_fast checker.

Run: python3 scripts/probes/probe_level1_pin.py        (~2-4 min)
"""

import itertools
import random
from collections import Counter
from math import comb

random.seed(371007)


class Domain:
    """The n-point smooth domain {g^i} in F_p with degree-d fit machinery
    (port of probe_subceiling_envelope.py)."""

    def __init__(self, p, g, n):
        self.P, self.G, self.N = p, g, n
        self.X = [pow(g, i, p) for i in range(n)]
        assert len(set(self.X)) == n and pow(g, n, p) == 1
        assert pow(g, n // 2, p) == p - 1
        self._bases = {}

    def _basis(self, base):
        base = tuple(base)
        hit = self._bases.get(base)
        if hit is not None:
            return hit
        P, X = self.P, self.X
        out = []
        for i in base:
            num = [1]
            den = 1
            for k in base:
                if k != i:
                    new = [0] * (len(num) + 1)
                    for a, ca in enumerate(num):
                        new[a + 1] = (new[a + 1] + ca) % P
                        new[a] = (new[a] - ca * X[k]) % P
                    num = new
                    den = den * (X[i] - X[k]) % P
            inv = pow(den, P - 2, P)
            out.append([c * inv % P for c in num])
        self._bases[base] = out
        return out

    def coeffs(self, base, y):
        P = self.P
        basis = self._basis(base)
        cs = [0] * len(basis[0])
        for bi, i in zip(basis, base):
            yi = y[i] % P
            for a, ca in enumerate(bi):
                cs[a] = (cs[a] + yi * ca) % P
        return cs

    def evalp(self, cs, x):
        P, acc = self.P, 0
        for c in reversed(cs):
            acc = (acc * x + c) % P
        return acc

    def fits(self, idxs, y, d):
        idxs = list(idxs)
        if len(idxs) <= d + 1:
            return True
        cs = self.coeffs(idxs[: d + 1], y)
        return all(self.evalp(cs, self.X[t]) == y[t] % self.P for t in idxs[d + 1:])

    def defect(self, R, y, d):
        R = list(R)
        cs = self.coeffs(R[: d + 1], y)
        return (y[R[-1]] - self.evalp(cs, self.X[R[-1]])) % self.P

    def bad_fast(self, u0, u1, gamma, t, d):
        """Complete checker: exists (d+1)-subset-generated poly with agreement >= t
        and u1 not fit on the agreement set."""
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(self.N)]
        for B in itertools.combinations(range(self.N), d + 1):
            cs = self.coeffs(B, ug)
            A = [i for i in range(self.N) if self.evalp(cs, X[i]) == ug[i]]
            if len(A) >= t and not self.fits(A, u1, d):
                return True
        return False

    def bad_candidates_mult(self, u0, u1, d):
        """defect-ratio candidates with their unfit-subset multiplicity."""
        P = self.P
        cnt = Counter()
        for R in itertools.combinations(range(self.N), d + 2):
            d1 = self.defect(R, u1, d)
            if d1 != 0:
                d0 = self.defect(R, u0, d)
                cnt[(-d0) * pow(d1, P - 2, P) % P] += 1
        return cnt

    def count_bad(self, u0, u1, t, d, prefilter=True):
        """Exact #bad at threshold t (>= d+3).  Prefilter (proven sound, ownership
        law): a bad scalar's defect-ratio multiplicity is >= ceil(C(t,d+1)/(d+2))."""
        cnt = self.bad_candidates_mult(u0, u1, d)
        floor_mult = -(-comb(t, d + 1) // (d + 2)) if prefilter else 1
        return sum(1 for g, m in cnt.items()
                   if m >= floor_mult and self.bad_fast(u0, u1, g, t, d))


def monomial(dom, e):
    return [pow(x, e, dom.P) for x in dom.X]


def spectrum_N(nu, rp):
    h = 2 ** (nu - 1)
    tot = 0
    for a in range(rp % 2, min(rp, h) + 1, 2):
        if (rp - a) // 2 <= h - a:
            tot += 2 ** a * comb(h, a)
    return tot


# -------------------------------------------------------- P0: prefilter soundness

def check_prefilter(dom, d, t, stacks, tag):
    """Cross-validate the multiplicity prefilter against the unfiltered count."""
    for (u0, u1) in stacks:
        a = dom.count_bad(u0, u1, t, d, prefilter=True)
        b = dom.count_bad(u0, u1, t, d, prefilter=False)
        assert a == b, (tag, a, b)
    print(f"   P0 prefilter sound on {len(stacks)} stacks ({tag})")


# -------------------------------------------------------- instance A: n=16, d=2

def instance_A(p, g, monomial_sweep=True, climb_iters=200, tag=""):
    n, d = 16, 2
    dom = Domain(p, g, n)
    print(f"== instance A (n=16, d=2) at p={p}, g={g} {tag} ==")

    # P1: the floor stack (X^8, X^4) -- level-2 family, 8-point fibers
    lvl2 = (monomial(dom, 8), monomial(dom, 4))
    lvl1 = (monomial(dom, 6), monomial(dom, 4))
    c7 = dom.count_bad(lvl2[0], lvl2[1], 7, d)
    c8 = dom.count_bad(lvl2[0], lvl2[1], 8, d)
    l1_at7 = dom.count_bad(lvl1[0], lvl1[1], 7, d)
    l1_at6 = dom.count_bad(lvl1[0], lvl1[1], 6, d)
    print(f"   P1 level-2 stack (X^8,X^4): #bad(t=7) = {c7}, #bad(t=8) = {c8} "
          f"(spectrum N(2,2) = {spectrum_N(2, 2)})")
    print(f"      level-1 stack (X^6,X^4): #bad(t=6) = {l1_at6} (N(3,3) = "
          f"{spectrum_N(3, 3)}), #bad(t=7) = {l1_at7} (family dies above its radius)")

    check_prefilter(dom, d, 7, [lvl2, lvl1,
                                (monomial(dom, 5), monomial(dom, 7)),
                                ([random.randrange(p) for _ in range(n)],
                                 [random.randrange(p) for _ in range(n)])],
                    f"A p={p}")

    best, arg = 0, None
    seen = []

    def consider(u0, u1, label):
        nonlocal best, arg
        c = dom.count_bad(u0, u1, 7, d)
        seen.append((c, label))
        if c > best:
            best, arg = c, label
        return c

    consider(lvl2[0], lvl2[1], "level-2 (X^8,X^4)")
    consider(lvl1[0], lvl1[1], "level-1 (X^6,X^4)")
    # the antipodal pencil (the discovery): all 16 scalars of -1/<g> bad at t <= 9
    pencil = (monomial(dom, 8), monomial(dom, 9))
    c_pencil = consider(pencil[0], pencil[1], "antipodal pencil (X^8,X^9)")
    orbit = set((-pow(x, p - 2, p)) % p for x in dom.X)
    orbit_bad = sum(1 for gam in orbit if dom.bad_fast(pencil[0], pencil[1], gam, 9, d))
    print(f"   P1b antipodal pencil (X^8,X^9): #bad(t=7) = {c_pencil}; inversion orbit "
          f"size {len(orbit)}, all bad at t=9: {orbit_bad} (radius 7/16 < 1/2)")
    assert orbit_bad == 16

    # P2: monomial sweep
    if monomial_sweep:
        mbest, marg = 0, None
        for e0 in range(n):
            for e1 in range(n):
                c = consider(monomial(dom, e0), monomial(dom, e1),
                             f"monomial ({e0},{e1})")
                if c > mbest:
                    mbest, marg = c, (e0, e1)
        print(f"   P2 monomial sweep 16x16: max #bad(t=7) = {mbest} at {marg}")

    # P3: adversarial structured families around the maximizer
    #  (a) code shifts and scalings: (a*X^8 + q(X), b*X^4 + q'(X)), q,q' deg<=2
    for _ in range(40):
        a, b = random.randrange(1, p), random.randrange(1, p)
        q = [random.randrange(p) for _ in range(3)]
        qp = [random.randrange(p) for _ in range(3)]
        u0 = [(a * lvl2[0][i] + dom.evalp(q, dom.X[i])) % p for i in range(n)]
        u1 = [(b * lvl2[1][i] + dom.evalp(qp, dom.X[i])) % p for i in range(n)]
        consider(u0, u1, "code-shift/scale of level-2")
    #  (b) single/double point deviations of the level-2 stack
    for _ in range(80):
        u0, u1 = list(lvl2[0]), list(lvl2[1])
        for _ in range(random.randrange(1, 3)):
            (u0 if random.randrange(2) == 0 else u1)[random.randrange(n)] = \
                random.randrange(p)
        consider(u0, u1, "deviated level-2")
    #  (c) splices of level-1 and level-2 directions
    for _ in range(40):
        a, b = random.randrange(p), random.randrange(p)
        u0 = [(lvl2[0][i] + a * lvl1[0][i]) % p for i in range(n)]
        u1 = [(lvl2[1][i] + b * monomial(dom, 5)[i]) % p for i in range(n)]
        consider(u0, u1, "level-1/2 splice")
    #  (d) random stacks
    for _ in range(40):
        consider([random.randrange(p) for _ in range(n)],
                 [random.randrange(p) for _ in range(n)], "random")
    #  (e) hill-climb (random edits; at p=17 also exhaustive greedy single edits)
    cur = (list(lvl2[0]), list(lvl2[1]))
    cur_c = c7
    for _ in range(climb_iters):
        u0, u1 = list(cur[0]), list(cur[1])
        for _ in range(random.randrange(1, 3)):
            (u0 if random.randrange(2) == 0 else u1)[random.randrange(n)] = \
                random.randrange(p)
        c = dom.count_bad(u0, u1, 7, d)
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    if cur_c > best:
        best, arg = cur_c, "hill-climb"
    if p == 17:
        # exhaustive greedy: all single-point edits, repeat until no improvement
        cur = (list(lvl2[0]), list(lvl2[1]))
        cur_c = c7
        improved = True
        rounds = 0
        while improved and rounds < 6:
            improved = False
            rounds += 1
            for side in range(2):
                for i in range(n):
                    old = cur[side][i]
                    for v in range(p):
                        if v == old:
                            continue
                        cur[side][i] = v
                        c = dom.count_bad(cur[0], cur[1], 7, d)
                        if c > cur_c:
                            cur_c = c
                            improved = True
                            old = v
                        else:
                            cur[side][i] = old
        print(f"   P3 exhaustive greedy (p=17) from level-2 stack: {cur_c}")
        if cur_c > best:
            best, arg = cur_c, "greedy p=17"
    print(f"   P3 adversarial max #bad(t=7) = {best}  [{arg}]")
    print()
    return best


# -------------------------------------------------------- instance B: n=16, d=4

def instance_B(p, g):
    n, d = 16, 4
    dom = Domain(p, g, n)
    print(f"== instance B (n=16, d=4, rate 5/16) at p={p}, g={g} ==")
    # level-1 rung r'_1 = 4 (radius 1/2, K_1 = 16, N_1 = 41); threshold below = 9
    # level-2 rung r'_2 = 3 (radius 1/4): stack (X^12, X^8), 12-point fibers
    lvl2 = (monomial(dom, 12), monomial(dom, 8))
    lvl1 = (monomial(dom, 8), monomial(dom, 6))
    c9 = dom.count_bad(lvl2[0], lvl2[1], 9, d)
    l1_at8 = dom.count_bad(lvl1[0], lvl1[1], 8, d)
    l1_at9 = dom.count_bad(lvl1[0], lvl1[1], 9, d)
    print(f"   P4 level-2 stack (X^12,X^8): #bad(t=9) = {c9} "
          f"(spectrum N(2,3) = {spectrum_N(2, 3)})")
    print(f"      level-1 stack (X^8,X^6): #bad(t=8) = {l1_at8} (N(3,4) = "
          f"{spectrum_N(3, 4)}), #bad(t=9) = {l1_at9}")
    best, arg = 0, None
    for e0 in range(n):
        for e1 in range(n):
            c = dom.count_bad(monomial(dom, e0), monomial(dom, e1), 9, d)
            if c > best:
                best, arg = c, (e0, e1)
    print(f"   P4 monomial sweep: max #bad(t=9) = {best} at {arg}")
    cur = (list(lvl2[0]), list(lvl2[1]))
    cur_c = c9
    for _ in range(120):
        u0, u1 = list(cur[0]), list(cur[1])
        for _ in range(random.randrange(1, 3)):
            (u0 if random.randrange(2) == 0 else u1)[random.randrange(n)] = \
                random.randrange(p)
        c = dom.count_bad(u0, u1, 9, d)
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    best = max(best, cur_c)
    print(f"   P4 adversarial max #bad(t=9) = {best}")
    print()
    return best


def main():
    # the engine values and scheme caps (P5 budget table inputs)
    engine_t7 = comb(16, 3) * 13 // comb(7, 3)
    cap_t7 = comb(16, 4) // comb(7, 4)
    realizable_floor = comb(16, 4) // comb(6, 3)
    print("-- P5 budget table (n=16, d=2, level-1 rung 5/8) --")
    print(f"   provable bad side K_1 = {2 ** 3 * comb(4, 3)}, exact N_1 = "
          f"{spectrum_N(3, 3)}; floor (level-2) N_2 = {spectrum_N(2, 2)}")
    print(f"   ownership engine at threshold 7 (pairs, w0=6): {engine_t7}")
    print(f"   absolute per-witness subset-counting cap C(16,4)/C(7,4) = {cap_t7}")
    print(f"   realizable scheme floor C(16,4)/C(6,3) = {realizable_floor}")
    print(f"   => the scheme cannot certify <= 31: cap {cap_t7} > 31. "
          f"The good side must be a named obligation.\n")

    w7 = []
    w7.append(instance_A(97, 8, monomial_sweep=True, climb_iters=200, tag="(main)"))
    w7.append(instance_A(17, 3, monomial_sweep=True, climb_iters=120,
                         tag="(tiny field, exhaustive greedy)"))
    w7.append(instance_A(12289, 4134, monomial_sweep=False, climb_iters=40,
                         tag="(the Lean instance; structured families only)"))

    wB = instance_B(97, 8)

    print("-- VERDICT --")
    print(f"   instance A observed W_7 (per field 97/17/12289): {w7}")
    print(f"   floor 5 <= W_7; pin band needs W_7 <= 31 (provable bad side 32)")
    for w in w7:
        assert w >= 5, "the level-2 floor must appear"
    if max(w7) <= 31:
        print(f"   -> CONSISTENT with the level-1 pin: observed worst {max(w7)} <= 31")
    else:
        print(f"   -> REFUTATION CANDIDATE: observed worst {max(w7)} > 31 !!")
    print(f"   instance B observed worst at t=9: {wB} (provable bad side K_1 = 16)")
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
