#!/usr/bin/env python3
"""Probe the level-j sub-ceiling bad-line ENVELOPE (#371, SubCeilingLadder.lean).

THE FAMILY.  Fix the code C = evalCode g n d (degree-<= d words on the smooth domain
x_i = g^i, n = 2^mu, orderOf g = n; m = 1 throughout, so the KKH26 slice parameter is
r = d + 2 and the in-tree ceiling radius is 1 - r/2^mu).  The in-tree KKH26 witness
(level 0) is the sign-subset construction at Y = X: stack (X^r, X^{r-1}), bad scalars
lambda_T = -sum(T) over r-subsets T of the full 2^mu-group, fiber witnesses of size r.

LEVEL j >= 1: substitute Y = X^{2^j} -- run the SAME construction on the order-2^{mu-j}
subgroup G_j = <g^{2^j}>: stack (X^{r'*2^j}, X^{(r'-1)*2^j}), bad scalars
lambda_T = -sum(T) over r'-subsets T of G_j, fiber witnesses of size r'*2^j, radius
1 - r'/2^{mu-j}.  The construction is bad for C iff BOTH
    (r'-2)*2^j <= d        (the gap-expansion remainder stays inside the code), and
    d < (r'-1)*2^j         (the direction X^{(r'-1)*2^j} is NOT a codeword -- otherwise
                            the joint pair (q - gamma*u1, u1) explains and the scalar is
                            GOOD; verified in S5 below),
which forces the UNIQUE per-level rung  r'_j = floor(d / 2^j) + 2.

THE STAIRCASE.  Level j contributes radius delta_j = 1 - r'_j/2^{mu-j} (strictly below
the KKH26 ceiling for every j >= 1), provable count K_j = 2^{r'_j} * C(2^{mu-j-1}, r'_j)
(the in-tree kkh26_lemma1 term, needs r'_j <= 2^{mu-j-1} and the level prime threshold
(2^{mu-j})^{2^{mu-j-1}} < p), exact count N_j = the TwoPowerSubsetSumSpectrum law
N(mu-j, r'_j) = sum_{a == r' (2), (r'-a)/2 <= h-a} 2^a*C(h,a), h = 2^{mu-j-1}.

THE ENVELOPE (candidate production-shape answer, bad side):
    deltaStar(C, eps*) <= min{ delta_j : level j valid, eps* * p < N_j }
-- the deepest biting level wins; the landed pins are the j = 0 rungs (where the budget
band [C(n,d+2)/2, 2^r*C(h,r))/p sits ABOVE every deeper level's count, see S4).

WHAT THIS PROBE CHECKS (exact, no sampling unless labelled):
  S1  per-instance level tables: enumerated distinct-lambda counts vs the spectrum law
      N_j and the lemma-1 term K_j; EVERY enumerated lambda verified bad through its
      constructive fiber witness (agreement of the line point + non-fit of the direction
      => the mcaEvent fires, (E) <=> (D) given the witness, see S3).
  S2  exact TOTAL bad count of the level-j stack at its threshold via the exhaustive
      (d+2)-defect candidate sweep (every bad scalar is a defect ratio on an owned
      (d+2)-set) -- is the subset-sum family the WHOLE bad set at its radius?
  S3  three-checker cross-validation (exhaustive mcaEvent / derived / fast) at p = 97 on
      sampled gammas (pattern of probe_dim3_interior_ceiling.py).
  S4  PIN SAFETY: at every landed pin instance the level-(j>=1) counts sit strictly
      below the band bottom C(n, d+2)/2, so the proven pins are untouched (they must
      be -- the ownership theorem covers these witnesses; this locates exactly where the
      level-j counts enter the budget); plus F5/F17 parameter vacuity.
  S5  the one-rung-per-level law: r' < r'_j at the same level is NOT bad (the direction
      becomes a codeword and the joint pair explains).
  S6  good-side gap: hill-climbed max bad count at threshold t_1 + 1 (just below the
      level-1 radius) at the first biting instance -- how far the ownership engine is
      from PINNING the sub-ceiling rung.

Run: python3 scripts/probes/probe_subceiling_envelope.py        (~3-5 min)
"""

import itertools
import random
from fractions import Fraction
from math import comb

random.seed(371)


# ---------------------------------------------------------------- the staircase laws

def spectrum_N(nu, rp):
    """Exact subset-sum spectrum N(nu, rp) of the 2-power group of order 2^nu
    (TwoPowerSubsetSumSpectrum law); the truth above the injectivity threshold."""
    h = 2 ** (nu - 1)
    tot = 0
    for a in range(rp % 2, min(rp, h) + 1, 2):
        if (rp - a) // 2 <= h - a:
            tot += 2 ** a * comb(h, a)
    return tot


def level_rows(mu, d):
    """All level rungs for the degree-d code on the 2^mu domain (m = 1).
    Rows: (j, nu, rp, t, delta, K_or_None, N_spec)."""
    rows = []
    for j in range(0, mu):
        nu = mu - j
        rp = d // (2 ** j) + 2
        if rp > 2 ** nu:
            continue
        rows.append((j, nu, rp, rp * 2 ** j, Fraction(2 ** nu - rp, 2 ** nu),
                     2 ** rp * comb(2 ** (nu - 1), rp) if rp <= 2 ** (nu - 1) else None,
                     spectrum_N(nu, rp)))
    return rows


# ---------------------------------------------------------------- field machinery

class Domain:
    """The n-point smooth domain {g^i} in F_p, with degree-d fits via cached
    Lagrange bases (coefficient form, Horner evaluation)."""

    def __init__(self, p, g, n):
        self.P, self.G, self.N = p, g, n
        self.X = [pow(g, i, p) for i in range(n)]
        assert len(set(self.X)) == n and pow(g, n, p) == 1
        assert pow(g, n // 2, p) == p - 1
        self._bases = {}

    def _basis(self, base):
        """Lagrange basis polynomials (coefficient vectors) for the nodes X[i], i in
        base; cached -- they do not depend on the interpolated word."""
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
        """coefficients of the poly through (X[i], y[i]), i in base."""
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
        """y|idxs is a degree-<= d polynomial evaluation."""
        idxs = list(idxs)
        if len(idxs) <= d + 1:
            return True
        cs = self.coeffs(idxs[: d + 1], y)
        return all(self.evalp(cs, self.X[t]) == y[t] % self.P for t in idxs[d + 1:])

    def defect(self, R, y, d):
        """(d+2)-point interpolation defect (linear in y; 0 iff y fits on R)."""
        R = list(R)
        cs = self.coeffs(R[: d + 1], y)
        return (y[R[-1]] - self.evalp(cs, self.X[R[-1]])) % self.P

    # --- the three badness checkers (general-d port of probe_dim3) ---

    def bad_fast(self, u0, u1, gamma, t, d):
        """(F) exists (d+1)-subset-generated poly with agreement >= t and u1 not fit
        on the agreement set.  Complete: any witness S is contained in the agreement
        set of each of its (d+1)-subsets, and non-fitting is upward-monotone."""
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(self.N)]
        for B in itertools.combinations(range(self.N), d + 1):
            cs = self.coeffs(B, ug)
            A = [i for i in range(self.N) if self.evalp(cs, X[i]) == ug[i]]
            if len(A) >= t and not self.fits(A, u1, d):
                return True
        return False

    def bad_exhaustive(self, u0, u1, gamma, t, d):
        """(E) literal mcaEvent: exists S, |S| >= t, ug|S fit, NOT (u0 and u1 fit)."""
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(self.N)]
        for s in range(t, self.N + 1):
            for S in itertools.combinations(range(self.N), s):
                if self.fits(S, ug, d) and not (self.fits(S, u0, d)
                                                and self.fits(S, u1, d)):
                    return True
        return False

    def bad_derived(self, u0, u1, gamma, t, d):
        """(D) exists S, |S| >= t, ug|S fit, u1|S not fit."""
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(self.N)]
        for s in range(t, self.N + 1):
            for S in itertools.combinations(range(self.N), s):
                if self.fits(S, ug, d) and not self.fits(S, u1, d):
                    return True
        return False

    def bad_candidates(self, u0, u1, d):
        """every bad scalar (threshold >= d+2) satisfies
        defect_R(u0) + gamma*defect_R(u1) = 0 on some (d+2)-subset R with
        defect_R(u1) != 0 => this candidate set is exhaustive."""
        P = self.P
        cands = set()
        for R in itertools.combinations(range(self.N), d + 2):
            d1 = self.defect(R, u1, d)
            if d1 != 0:
                d0 = self.defect(R, u0, d)
                cands.add((-d0) * pow(d1, P - 2, P) % P)
        return cands

    def count_bad_via_candidates(self, u0, u1, t, d):
        return sum(1 for g in self.bad_candidates(u0, u1, d)
                   if self.bad_fast(u0, u1, g, t, d))


def monomial(dom, e):
    return [pow(x, e, dom.P) for x in dom.X]


# ---------------------------------------------------------------- per-instance run

def run_instance(tag, p, g, mu, d, three_checker=False, exact_sweep_levels=()):
    n = 2 ** mu
    r = d + 2
    dom = Domain(p, g, n)
    print(f"== {tag}: p = {p}, g = {g}, n = {n}, d = {d} "
          f"(r = {r}, ceiling radius {Fraction(n - r, n)}) ==")
    results = []
    for (j, nu, rp, t, delta, K, Nspec) in level_rows(mu, d):
        # sanity: the unique-rung inequalities
        assert (rp - 2) * 2 ** j <= d < (rp - 1) * 2 ** j
        Gj = [pow(g, (2 ** j) * i, p) for i in range(2 ** nu)]
        assert len(set(Gj)) == 2 ** nu
        lam2T = {}
        for T in itertools.combinations(Gj, rp):
            lam2T.setdefault((-sum(T)) % p, T)
        u0 = monomial(dom, rp * 2 ** j)
        u1 = monomial(dom, (rp - 1) * 2 ** j)
        # constructive badness of EVERY enumerated lambda via its fiber witness
        for lam, T in lam2T.items():
            ug = [(u0[i] + lam * u1[i]) % p for i in range(n)]
            S = [i for i in range(n) if pow(dom.X[i], 2 ** j, p) in set(T)]
            assert len(S) == t, (j, rp, len(S))
            assert dom.fits(S, ug, d), "line point does NOT fit on its fiber!"
            assert not dom.fits(S, u1, d), "direction FITS on the fiber (joint pair)!"
        cnt = len(lam2T)
        hp_ok = (2 ** nu) ** (2 ** (nu - 1)) < p
        flag = "LEMMA" if K is not None else "exist"
        print(f"  level j={j}: r'={rp}, threshold {t}, radius {delta} [{flag}] "
              f"K={K} N_spec={Nspec} | distinct bad lambdas = {cnt} "
              f"(all fiber-verified){' [hp_j holds]' if hp_ok else ''}")
        if K is not None and hp_ok:
            assert cnt >= K, "lemma-1 count violated above the level prime threshold!"
        results.append((j, rp, t, delta, K, Nspec, cnt))

        # S2: exact TOTAL bad count of this stack at this threshold
        if j in exact_sweep_levels:
            total = dom.count_bad_via_candidates(u0, u1, t, d)
            extra = total - cnt
            print(f"      S2 exact bad count of the level-{j} stack at threshold {t}: "
                  f"{total} = subset-sum family {cnt} + {extra} extra")
            assert total >= cnt

        # S3: three-checker cross-validation on sampled gammas
        if three_checker:
            lams = sorted(lam2T)
            sample = lams[:4] + [random.randrange(p) for _ in range(4)]
            for gam in sample:
                e = dom.bad_exhaustive(u0, u1, gam, t, d)
                dv = dom.bad_derived(u0, u1, gam, t, d)
                f = dom.bad_fast(u0, u1, gam, t, d)
                assert e == dv == f, (tag, j, gam, e, dv, f)
            print(f"      S3 3-checker (E/D/F) byte-exact on {len(sample)} gammas")

        # S5: one-rung-per-level law -- r' - 1 at the same level is NOT bad
        if rp - 1 >= 2:
            rs = rp - 1
            assert (rs - 1) * 2 ** j <= d, "sub-rung direction must be a codeword"
            u0s, u1s = monomial(dom, rs * 2 ** j), monomial(dom, (rs - 1) * 2 ** j)
            for T in list(itertools.combinations(Gj, rs))[:3]:
                assert not dom.bad_fast(u0s, u1s, (-sum(T)) % p, rs * 2 ** j, d)
            print(f"      S5 one-rung law: r'={rs} at level {j} NOT bad "
                  f"(direction X^{(rs - 1) * 2 ** j} is a codeword)")
    print()
    return results


def envelope_table(tag, results, band_bottom):
    print(f"-- envelope staircase, {tag} (band bottom C(n,d+2)/2 = {band_bottom}) --")
    for (j, rp, t, delta, K, Nspec, cnt) in sorted(results, key=lambda x: x[0]):
        print(f"   eps*·p < {cnt:>5} (provable: < K={K})  =>  "
              f"deltaStar <= {str(delta):>5}   (level {j}, r'={rp})")
    deeper = [c for (j, rp, t, delta, K, Nspec, c) in results if j >= 1]
    if deeper:
        mx = max(deeper)
        assert mx < band_bottom, "PIN CONFLICT (impossible -- the ownership thm bounds it)"
        print(f"   S4 PIN SAFETY: max level-(j>=1) count {mx} < band bottom "
              f"{band_bottom} -> the landed pin band is untouched")
    print()


# ---------------------------------------------------------------- main lanes

def main():
    # ---- landed-pin instances (mu = 3, n = 8, F12289, g = 4043 of order 8) ----
    res = run_instance("PIN r=2 (n=8, d=0, F12289)", 12289, 4043, 3, 0,
                       exact_sweep_levels=(0, 1, 2))
    envelope_table("PIN r=2", res, comb(8, 2) // 2)

    res = run_instance("PIN r=3 (n=8, d=1, F12289)", 12289, 4043, 3, 1,
                       exact_sweep_levels=(0, 1))
    envelope_table("PIN r=3", res, comb(8, 3) // 2)

    # ---- the r=4 rung family at n=16 (the dim-3 pin shape), F12289, g = 4134 ----
    res = run_instance("RUNG r=4 (n=16, d=2, F12289)", 12289, 4134, 4, 2,
                       exact_sweep_levels=(1, 2))
    envelope_table("RUNG r=4", res, comb(16, 4) // 2)

    # ---- the (mu=4, r=6) sub-max-rate shape: band EMPTY at level 0, the level-1
    # ----  16-lambda family at radius 1/2 < ceiling 5/8 (the attack-round numerics) ----
    run_instance("SUBMAX r=6 (n=16, d=4, F97)", 97, 8, 4, 4, three_checker=True,
                 exact_sweep_levels=(1,))
    res = run_instance("SUBMAX r=6 (n=16, d=4, F12289)", 12289, 4134, 4, 4)
    envelope_table("SUBMAX r=6", res, comb(16, 6) // 2)

    # ---- small-prime three-checker lane for the r=4 family ----
    run_instance("RUNG r=4 (n=16, d=2, F97)", 97, 8, 4, 2, three_checker=True,
                 exact_sweep_levels=(1, 2))

    # ---- S4b: F5 / F17 granularity pins -- the family is parameter-VACUOUS there ----
    for (tag, mu, d) in [("F5 pin (n=4, deg<2: mu=2, d=1)", 2, 1),
                         ("F17 pin (n=8, deg<4: mu=3, d=3)", 3, 3)]:
        rows = level_rows(mu, d)
        lemma_rows = [rw for rw in rows if rw[5] is not None]
        print(f"{tag}: lemma-regime rungs = {len(lemma_rows)}; "
              f"existence-only rungs = {[(rw[0], rw[2]) for rw in rows]}")
        assert not lemma_rows, "unexpected lemma rung at a granularity-pin instance"
    print("   -> the envelope is VACUOUS at the F5/F17 granularity pins: consistent.\n")

    # ---- S6: good-side gap at the first biting instance (n=16, d=2, level 1) ----
    print("-- S6 good-side gap (n=16, d=2, F97): max bad at threshold 7 "
          "(radius just below the level-1 rung 5/8) --")
    dom = Domain(97, 8, 16)
    stacks = [(monomial(dom, 6), monomial(dom, 4)), (monomial(dom, 4), monomial(dom, 3))]
    for e0 in range(5):
        for e1 in range(5):
            stacks.append((monomial(dom, e0), monomial(dom, e1)))
    for _ in range(10):
        stacks.append(([random.randrange(97) for _ in range(16)],
                       [random.randrange(97) for _ in range(16)]))
    best, arg = 0, stacks[0]
    for (u0, u1) in stacks:
        c = dom.count_bad_via_candidates(u0, u1, 7, 2)
        if c > best:
            best, arg = c, (u0, u1)
    cur, cur_c = arg, best
    for _ in range(60):
        u0, u1 = list(cur[0]), list(cur[1])
        for _ in range(random.randrange(1, 3)):
            (u0 if random.randrange(2) == 0 else u1)[random.randrange(16)] = \
                random.randrange(97)
        c = dom.count_bad_via_candidates(u0, u1, 7, 2)
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    best = max(best, cur_c)
    print(f"   hill-climbed max bad at threshold 7 = {best}; level-1 budget edge K_1 = 32 "
          f"(N_1 = 40); in-tree ownership good side = C(16,4)/2 = 910.")
    print(f"   -> PINNING deltaStar = 5/8 at eps* < 32/p needs a good side <= 32 at "
          f"threshold 7; observed worst stack = {best}; engine gives 910.  OPEN.\n")

    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
