#!/usr/bin/env python3
r"""Ownership census probe (#371 wall attack): the TRUE per-scalar ownership law.

The landed general ladder bound (Lean: dimGeneral_badScalars_card_mul_two_le,
KKH26DimGeneralPin.lean) gives each bad scalar >= 2 owned bad (d+2)-subsets via the
on-fit/off-fit split with claimed worst case (alpha, xi) = (d+1, 2).  THIS PROBE
re-derives the honest law:

  (LP THEOREM, provable)  for EVERY (d+1)-subset B of the witness S there is at least
  one x in S \ B with u1 NOT degree-d-fit on insert x B (otherwise u1 would be fit on
  all of S by the interpolant through B) -- so the owned (B, x) PAIRS number
  >= C(w, d+1), equivalently

      ownership * (d+2) >= C(w, d+1),        w = |S| >= t = r*m + 1.

  (EXACT LAW, conjectured + constructively attained)  the minimum ownership over all
  bad configurations with witness size w is

      min ownership = C(w-1, d+1)

  attained EXACTLY by the single-deviation stacks: u1 = (deg-<=d polynomial q) on
  S \ {j}, deviating at the single point j; then a (d+2)-subset T of S is unfit iff
  j in T, so ownership = C(w-1, d+1).  At the minimal witness w = t = r+1 (m = 1)
  this is C(r, r-1) = r -- NOT 2: the landed (d+1,2)-split worst case is unattainable
  for r >= 3 (it is exact only at r = 2, where C(w-1, 1) = w-1 = 2 at w = 3).

  (CEILING)  ownership <= C(w, d+2) trivially (= r+1 at w = t, m = 1): no
  per-witness-subset counting scheme can guarantee more than C(t-1, d+1) ~ r per
  scalar (the deviation stacks realize it), so the (d+2)-subset ownership war's wall
  is r ~ sqrt(2 n ln r) -- the LP theorem already saturates the scheme up to the
  additive ln 2 inside the log.

THE NEW WALL (band tables below): the sharpened floor

    #bad <= C(n, d+1) * (n-d-1) / C(t, d+1)     (t = r*m+1; = 2*C(n,r)/(r+1) at m=1)

against the ceiling spectrum 2^r * C(2^(mu-1), r); clean Lean criterion
r*(r+1) < 2^mu (vs landed r*(r-1) < 2^(mu-1): doubles the r^2 reach), true band
r ~ sqrt(2 n ln r) vs old 1.18 sqrt(n).  Newly opened rungs: (mu, r) = (4, 5)
[floor 1456 < 1792, old floor 2184 EMPTY -- the Lean instance lands at
p = 2^32 + 81], and (5, 7), (5, 8), (5, 9) [old max at mu=5 is r=6].

Run: python3 scripts/probes/probe_ownership_census.py
"""

import itertools
import random
from math import comb, isqrt

random.seed(371371)


# ---------------------------------------------------------------- arithmetic

class Dom:
    """Smooth domain x_i = g^i, i < n, in F_p; degree-<=d interpolation tools."""

    def __init__(self, p, g, n, d):
        self.p, self.g, self.n, self.d = p, g, n, d
        self.X = [pow(g, i, p) for i in range(n)]
        assert len(set(self.X)) == n, "g must have order >= n"
        assert pow(g, n, p) == 1, "orderOf g = n expected"

    def interp_eval_all(self, idxs, y):
        """Evaluations at ALL n domain points of the unique deg-<=|idxs|-1 polynomial
        through (X[i], y[i]) for i in idxs (Lagrange)."""
        p, X = self.p, self.X
        idxs = list(idxs)
        out = [0] * self.n
        for i in idxs:
            denom = 1
            for j in idxs:
                if j != i:
                    denom = denom * (X[i] - X[j]) % p
            ci = y[i] * pow(denom, p - 2, p) % p
            for k in range(self.n):
                num = 1
                for j in idxs:
                    if j != i:
                        num = num * (X[k] - X[j]) % p
                out[k] = (out[k] + ci * num) % p
        return out

    def fits(self, idxs, y):
        """y restricted to idxs is a deg-<=d polynomial evaluation."""
        idxs = list(idxs)
        if len(idxs) <= self.d + 1:
            return True
        base = idxs[: self.d + 1]
        ev = self.interp_eval_all(base, y)
        return all(ev[i] == y[i] for i in idxs)


# ------------------------------------------------------- bad-scalar machinery

def bad_scalars(dom, u0, u1, t):
    """All gamma with mcaEvent at threshold t, via: bad <=> exists codeword cw with
    agreement set A = {i : cw_i = u0_i + gamma u1_i}, |A| >= t, and u1 NOT fit on A.
    (Given the line fit on S, pairJointAgreesOn S <=> u1 fit on S; and u1 unfit on a
    superset A >= t implies an unfit subset witness of every size in [t, |A|].)
    Candidate sweep: codewords come from interpolating (d+1)-subsets; agreement of the
    B-interpolant with the line at gamma is {i : gamma*a_i = b_i} with
    a = L_B u1 - u1, b = u0 - L_B u0 -- per (B, i) a single gamma (or all/none)."""
    p, n, d = dom.p, dom.n, dom.d
    cand = set()
    for B in itertools.combinations(range(n), d + 1):
        v0 = dom.interp_eval_all(B, u0)
        v1 = dom.interp_eval_all(B, u1)
        a = [(v1[i] - u1[i]) % p for i in range(n)]
        b = [(u0[i] - v0[i]) % p for i in range(n)]
        base = sum(1 for i in range(n) if a[i] == 0 and b[i] == 0)
        assert base < t, "degenerate stack (line close at every gamma): not in census scope"
        hits = {}
        for i in range(n):
            if a[i] != 0:
                gam = b[i] * pow(a[i], p - 2, p) % p
                hits[gam] = hits.get(gam, 0) + 1
        for gam, h in hits.items():
            if base + h >= t:
                cand.add(gam)
    out = []
    for gam in sorted(cand):
        if maximal_agreement_sets(dom, u0, u1, gam, t):
            out.append(gam)
    return out


def maximal_agreement_sets(dom, u0, u1, gam, t):
    """Maximal agreement sets A (per codeword) with |A| >= t and u1 NOT fit on A."""
    p, n, d = dom.p, dom.n, dom.d
    y = [(u0[i] + gam * u1[i]) % p for i in range(n)]
    seen, out = set(), []
    for B in itertools.combinations(range(n), d + 1):
        cw = tuple(dom.interp_eval_all(B, y))
        if cw in seen:
            continue
        seen.add(cw)
        A = frozenset(i for i in range(n) if cw[i] == y[i])
        if len(A) >= t and not dom.fits(A, u1):
            if A not in (s for s, _ in out):
                out.append((A, cw))
    # dedupe by A
    uniq = {}
    for A, cw in out:
        uniq[A] = cw
    return list(uniq.keys())


def ownership(dom, S, u1):
    """#unfit (d+2)-subsets of S (the owned family of the scalar at witness S)."""
    d = dom.d
    return sum(1 for T in itertools.combinations(sorted(S), d + 2)
               if not dom.fits(T, u1))


def max_fit_locus(dom, S, u1):
    """Size of the largest subset of S on which u1 IS deg-<=d fit."""
    d = dom.d
    S = sorted(S)
    best = d + 1  # any (d+1)-subset is fit
    for B in itertools.combinations(S, d + 1):
        ev = dom.interp_eval_all(B, u1)
        locus = sum(1 for i in S if ev[i] == u1[i])
        best = max(best, locus)
    return best


def census_scalar(dom, u0, u1, gam, t):
    """Per-scalar census: for every valid witness (each maximal agreement set A, plus
    every size-t subset S of A with u1 unfit on S), record (w, ownership, locus);
    return the binding (minimum-ownership) witness stats + per-witness law checks."""
    d = dom.d
    recs = []
    for A in maximal_agreement_sets(dom, u0, u1, gam, t):
        worklist = [tuple(sorted(A))]
        if len(A) > t:
            worklist += [S for S in itertools.combinations(sorted(A), t)
                         if not dom.fits(S, u1)]
        for S in worklist:
            w = len(S)
            o = ownership(dom, S, u1)
            a = max_fit_locus(dom, S, u1)
            # the LP THEOREM (provable): ownership*(d+2) >= C(w, d+1)
            assert o * (d + 2) >= comb(w, d + 1), \
                f"LP LAW VIOLATED: o={o} w={w} d={d} gam={gam}"
            # the landed bound (sanity): >= 2
            assert o >= 2, f"landed >=2 violated: o={o}"
            # the conjectured EXACT law floor: ownership >= C(w-1, d+1)
            assert o >= comb(w - 1, d + 1), \
                f"EXACT LAW VIOLATED: o={o} < C({w - 1},{d + 1}) gam={gam}"
            recs.append((w, o, a))
    return recs


# ------------------------------------------------------- adversarial stacks

def deviation_stack(dom, t, rng):
    r"""The extremal single-deviation construction: u1 = q on S0 \ {j}, deviating at j;
    u0 = qS - u1 on S0 (gamma0 = 1); random off S0.  Realizes ownership C(t-1, d+1)."""
    p, n, d = dom.p, dom.n, dom.d
    S0 = sorted(rng.sample(range(n), t))
    j = S0[rng.randrange(t)]
    qc = [rng.randrange(p) for _ in range(d + 1)]
    qS = [rng.randrange(p) for _ in range(d + 1)]

    def ev(c, x):
        r, m = 0, 1
        for ci in c:
            r = (r + ci * m) % p
            m = m * x % p
        return r

    u1 = [rng.randrange(p) for _ in range(n)]
    u0 = [rng.randrange(p) for _ in range(n)]
    for i in S0:
        u1[i] = ev(qc, dom.X[i])
    u1[j] = (u1[j] + 1 + rng.randrange(p - 1)) % p
    for i in S0:
        u0[i] = (ev(qS, dom.X[i]) - u1[i]) % p
    return u0, u1, 1, frozenset(S0), j


# ---------------------------------------------------------------- instances

def find_order_elem(p, n):
    for b in range(2, 200):
        g = pow(b, (p - 1) // n, p)
        if pow(g, n, p) == 1 and all(pow(g, n // q, p) != 1 for q in (2,)):
            ords = {pow(g, k, p) for k in range(n)}
            if len(ords) == n:
                return g
    raise RuntimeError("no order-n element found")


def run_instance(p, n, mu, r, n_random=40, n_dev=25):
    d, t = r - 2, r + 1  # m = 1
    g = find_order_elem(p, n)
    dom = Dom(p, g, n, d)
    print(f"\n=== instance p={p} n={n} mu={mu} r={r} d={d} t={t} g={g} ===")
    print(f"  theory: LP floor ceil(C(w,{d + 1})/{d + 2}); exact law C(w-1,{d + 1}); "
          f"cap C(w,{d + 2}); at w=t: LP={-(-comb(t, d + 1) // (d + 2))}, "
          f"exact={comb(t - 1, d + 1)}, cap={comb(t, d + 2)}")

    rng = random.Random(p * 1000 + r)
    all_recs, glob_min = [], None

    # (i) the KKH26 ceiling stack (x^r, x^(r-1))
    u0 = [pow(dom.X[i], r, p) for i in range(n)]
    u1 = [pow(dom.X[i], r - 1, p) for i in range(n)]
    stacks = [("ceiling", u0, u1)]
    # (ii) random stacks
    for s in range(n_random):
        stacks.append(("random", [rng.randrange(p) for _ in range(n)],
                       [rng.randrange(p) for _ in range(n)]))

    per_stack_bad = []
    for tag, u0, u1 in stacks:
        bs = bad_scalars(dom, u0, u1, t)
        per_stack_bad.append((tag, len(bs)))
        for gam in bs:
            recs = census_scalar(dom, u0, u1, gam, t)
            if recs:
                m = min(o for _, o, _ in recs)
                all_recs += [(tag, gam, w, o, a) for w, o, a in recs]
                glob_min = m if glob_min is None else min(glob_min, m)

    n_bad_ceiling = per_stack_bad[0][1]
    n_bad_rand = sum(c for tg, c in per_stack_bad[1:])
    print(f"  bad scalars: ceiling stack {n_bad_ceiling}, "
          f"random stacks total {n_bad_rand}")

    # (iii) deviation-adversarial stacks: the exact-law extremals
    dev_hits = 0
    for s in range(n_dev):
        u0, u1, gam0, S0, j = deviation_stack(dom, t, rng)
        recs = census_scalar(dom, u0, u1, gam0, t)
        assert recs, "deviation scalar must be bad with witness S0"
        m = min(o for _, o, _ in recs)
        glob_min = m if glob_min is None else min(glob_min, m)
        if m == comb(t - 1, d + 1):
            dev_hits += 1
        all_recs += [("deviation", gam0, w, o, a) for w, o, a in recs]
    print(f"  deviation stacks: {dev_hits}/{n_dev} attain the exact-law minimum "
          f"C(t-1,d+1) = {comb(t - 1, d + 1)}")
    assert dev_hits > 0, "extremal construction must attain C(t-1, d+1) somewhere"

    # ownership census table vs (w, a)
    from collections import defaultdict
    tab = defaultdict(list)
    for tag, gam, w, o, a in all_recs:
        tab[(w, a)].append(o)
    print("  census (w, max-fit-locus a) -> [min..max] ownership  "
          "| LP floor | exact law C(w-1,d+1) | cap C(w,d+2)")
    for (w, a) in sorted(tab):
        os_ = tab[(w, a)]
        print(f"    w={w:3d} a={a:3d}: own in [{min(os_):6d},{max(os_):6d}] "
              f"x{len(os_):5d} | {-(-comb(w, d + 1) // (d + 2)):6d} "
              f"| {comb(w - 1, d + 1):6d} | {comb(w, d + 2):6d}")
    print(f"  GLOBAL min ownership = {glob_min} "
          f"(exact law at w=t: {comb(t - 1, d + 1)}; landed bound: 2)")
    return glob_min


# ------------------------------------------------------------- band tables

def wall_table():
    print("\n=== THE WALL TABLE (m = 1): max r with band nonempty, per mu ===")
    print("  floor_old  = C(n,r)/2                      (landed factor-2 ownership)")
    print("  floor_new  = C(n,r-1)*(n-r+1)/C(r+1,r-1)   (sharpened: pair ownership, "
          "= 2C(n,r)/(r+1))")
    print("  floor_xct  = C(n,r)/r                      (exact-law ownership "
          "C(t-1,d+1)=r; scheme-attainable)")
    print("  floor_cap  = C(n,r)/(r+1)                  (absolute cap C(t,d+2)=r+1: "
          "NO subset scheme beats this)")
    print("  ceiling    = 2^r * C(2^(mu-1), r)")
    hdr = f"  {'mu':>3} {'n':>5} {'old':>5} {'new':>5} {'xct':>5} {'cap':>5}" \
          f"  {'old/sqrt(n)':>11} {'new/sqrt(n)':>11} {'cap/sqrt(n)':>11}"
    print(hdr)
    for mu in range(3, 11):
        n, h = 2 ** mu, 2 ** (mu - 1)
        mx = {"old": 0, "new": 0, "xct": 0, "cap": 0}
        for r in range(2, h + 1):
            ceil_ = 2 ** r * comb(h, r)
            if comb(n, r) // 2 < ceil_:
                mx["old"] = r
            if (comb(n, r - 1) * (n - r + 1)) // comb(r + 1, r - 1) < ceil_:
                mx["new"] = r
            if comb(n, r) // r < ceil_:
                mx["xct"] = r
            if comb(n, r) // (r + 1) < ceil_:
                mx["cap"] = r
        s = n ** 0.5
        print(f"  {mu:>3} {n:>5} {mx['old']:>5} {mx['new']:>5} {mx['xct']:>5} "
              f"{mx['cap']:>5}  {mx['old'] / s:>11.3f} {mx['new'] / s:>11.3f} "
              f"{mx['cap'] / s:>11.3f}")
    print("  -> the sharpened wall tracks sqrt(2 n ln r) (the old one sqrt(2 n ln 2));")
    print("     'cap' shows the (d+2)-subset ownership scheme CANNOT be pushed past")
    print("     r ~ sqrt(n log n) by ANY further sharpening: the deviation stacks")
    print("     pin per-scalar ownership at C(t-1,d+1), and the trivial cap is C(t,d+2).")


def lean_instance_numbers():
    print("\n=== Lean instance arithmetic (exact) ===")
    # the new rung (mu, r) = (4, 5): floor / band
    fl = comb(16, 4) * (16 - 4) // comb(6, 4)
    print(f"  (mu,r)=(4,5): new floor C(16,4)*12/C(6,4) = {comb(16, 4)}*12/{comb(6, 4)}"
          f" = {fl}; ceiling 2^5*C(8,5) = {2 ** 5 * comb(8, 5)};"
          f" old floor C(16,5)/2 = {comb(16, 5) // 2} (EMPTY: >= ceiling)")
    assert fl == 1456 and 2 ** 5 * comb(8, 5) == 1792 and comb(16, 5) // 2 == 2184
    assert fl < 1792 <= comb(16, 5) // 2
    # delta* = 11/16 window position at rate 1/4
    print("  delta* = 1 - 5/16 = 11/16 = 0.6875; rate (r-1)/16 = 1/4;"
          " Johnson 1-sqrt(1/4) = 0.5 < 0.6875 < 0.75 = capacity  [IN-WINDOW]")
    # mu = 5 reach
    for r in (7, 8, 9):
        a = comb(32, r - 1) * (32 - r + 1) // comb(r + 1, r - 1)
        c = 2 ** r * comb(16, r)
        o = comb(32, r) // 2
        print(f"  (mu,r)=(5,{r}): new floor {a} < ceiling {c}; old floor {o} "
              f"({'EMPTY' if o >= c else 'open'})")
        assert a < c
        assert o >= c  # all three rungs newly opened
    # criterion check: r(r+1) < 2^mu (clean Lean criterion)
    for mu, r in [(4, 3), (5, 5), (6, 7), (7, 10), (8, 15)]:
        assert r * (r + 1) < 2 ** mu, (mu, r)
        a = comb(2 ** mu, r - 1) * (2 ** mu - r + 1) // comb(r + 1, r - 1)
        assert a < 2 ** r * comb(2 ** (mu - 1), r), f"criterion failed mu={mu} r={r}"
    print("  clean criterion r(r+1) < 2^mu verified against direct evaluation"
          " at (4,3),(5,5),(6,7),(7,10),(8,15)")


def main():
    print("#371 ownership census probe -- the sharpened per-scalar ownership law")
    wall_table()
    lean_instance_numbers()

    # full censuses (m = 1 instances; p = 12289 has 2^12 | p-1: orders 8 and 16 exist)
    run_instance(12289, 8, 3, 2)            # d = 0 (the r=2 rung)
    run_instance(12289, 8, 3, 3)            # d = 1 (the r=3 rung)
    run_instance(12289, 16, 4, 4, n_random=25, n_dev=20)   # d = 2 (the r=4 rung)
    run_instance(12289, 16, 4, 5, n_random=20, n_dev=20)   # d = 3 (the NEW r=5 rung)

    print("\nALL ASSERTIONS PASSED")
    print("the law: ownership*(d+2) >= C(w,d+1) [provable, Lean target];"
          " true min = C(w-1,d+1) [deviation-attained];"
          " cap C(w,d+2) [scheme ceiling]")


if __name__ == "__main__":
    main()
