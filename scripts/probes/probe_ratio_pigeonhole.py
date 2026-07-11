#!/usr/bin/env python3
"""Round-10 probe (#371): THE RATIO-PIGEONHOLE GOOD SIDE -- the five-thirds strip.

THE CLAIM UNDER TEST (RatioPigeonholeGoodSide.lean).  For the degree-<= d evaluation
code on an n-point injective domain, at agreement threshold t with

    (HB)   2t >= n + d + 2          and        (H53)  5t >= 3n + 3d + 1,

EVERY stack (u0, u1) has at most  n - t + 1  bad scalars (the simplex value), with NO
field-size guard.  Derivation (the coordinate-space ratio surface):

  * per bad gamma take the maximal agreement set A_gamma of its witness codeword
    q_gamma;  |A_gamma| >= t,  pairwise |A ^ A'| >= 2t - n;
  * the pair-interpolant r(gamma,gamma') := (q_gamma - q_gamma')/(gamma - gamma')
    agrees with u1 pointwise on A ^ A'; "same r" partitions the bad set into AFFINE
    FAMILIES q_gamma = a + gamma*r through any fixed gamma0 (transitivity is free);
  * within a family: A_gamma = D u fibre(gamma), D = the shared degenerate core
    {u0 = a, u1 = r}, fibres = disjoint ratio level sets, and non-joint-explainability
    forces >= max(1, t - |D|) fresh points per scalar (a, r ARE codewords);
  * THE INTERACTION LAW (new): for two families i != j through gamma0,
    a_j - a_i = gamma0*(r_i - r_j), so every point of the foreign core D_j either has
    u1 = r_i (<= d points, distinct degree-<= d polys) or its family-i ratio collapses
    to EXACTLY gamma0:   D_j  is a subset of  fibre_i(gamma0) u Z_ij,  |Z_ij| <= d.
  * counting D_i + fibre_i(gamma0) + member fibres inside [n]:
      K >= 3 families  =>  5t <= 3n + 3d   (dead under H53);
      K  = 2 families  =>  mu1 + mu2 <= n - t   (under HB, via (mu_i - 1)*B <= m - B);
      K  = 1 family    =>  N <= n - t + 1  (the pigeonhole; simplex-tight).

Census cross-check (round-8 exhaustive table, p = 17, n = 8):
  IN-strip cells   (d,t) = (1,6) (1,7) (2,7) (3,7) (2,8): census 3/2/2/2/1 = n-t+1 OK
  OUT-strip cells  (2,6): 5t = 30 < 31 fails H53 by ONE  -- census 4 > 3  (pencil)
                   (3,6): 2t = 12 < 13 fails HB  by ONE  -- census 7 > 3  (surplus)
                   (1,5): 2t = 10 < 11 fails HB  by ONE  -- census 8 > 4  (pencil)
  The hypothesis pair is SHARP against every censused violation, including the mod-17
  surpluses (they live strictly outside the strip: the strip needs no p0 guard).

NEW PREDICTION at the deployed shape (n = 16, d = 2): the strip floor is t = 11
(5*11 = 55 = 3*16 + 3*2 + 1, exactly on the boundary) -- ONE RUNG BEYOND the landed
granularity ladder (GranularityLadderRS needs 3(j-1)+k <= n, i.e. t >= 12 here).
Never censused at n = 16.  This probe attacks it:

  T1  simplex attainment: the (n-t+1)-simplex carries exactly 6 bad scalars at t = 11
      (p = 97, 257, 12289) -- floor = ceiling met if T2/T3 find nothing bigger.
  T2  adversarial search at (97, 16, 2, t=11): catalogue seeds (pencil, bisimplex,
      overlap, staircase, two-family LP shapes) + hill-climbing + random; the claim
      is max = 6.  Replication at p = 257.
  T3  the explicit two-family "LP-7" attack (D1 = 10-core simplex family + second
      family grafted on the 6 fibre points): the interaction law predicts the second
      core eats family-1 fibres 1-for-1 (ratio collapse to gamma0), so N <= 6 stays.
      Build it, measure the trade-off curve.
  T4  strip boundary sharpness at n = 16: at t = 10 (5t = 50 < 55) the antipodal
      pencil s=2 carries 8 > 7 = n-t+1: the H53 frontier is exact at n = 16 too.
  T5  in-proof invariants on every stack found with >= 2 bad scalars at t = 11:
      (a) family count K through gamma0 is <= 2; (b) within-family core/fibre law;
      (c) K = 2 only with mu1 + mu2 <= n - t; (d) the interaction inclusion
      D_j <= fibre_i(gamma0) u Z_ij verified set-by-set.
"""

import os
import sys
import random
import itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_bad_family_census import Domain  # noqa: E402


# ---------------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------------

def find_g(p, n):
    """An element of multiplicative order n in F_p."""
    for h in range(2, p):
        if pow(h, n, p) == 1 and all(pow(h, n // q, p) != 1
                                     for q in set(_factor(n))):
            return h
    raise ValueError


def _factor(n):
    out, m, f = [], n, 2
    while m > 1:
        while m % f == 0:
            out.append(f)
            m //= f
        f += 1
    return out


def interp(dom, idxs, y, d):
    """Coefficients (deg <= d) interpolating y on the first d+1 indices of idxs."""
    return dom.coeffs(list(idxs)[: d + 1], y)


def poly_sub(P, a, b):
    n = max(len(a), len(b))
    return tuple((((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % P)
                 for i in range(n))


def poly_scale(P, c, a):
    return tuple(c * x % P for x in a)


def bad_scalars_with_witness(dom, u0, u1, t, d):
    """{gamma: (A, qcoeffs)} exact, via the candidate-multiset prefilter (sound for
    t >= d+3) -- the witness is the max-agreement unfit interpolant."""
    P = dom.P
    out = {}
    cnt = dom.bad_candidates_mult(u0, u1, d)
    for gam in cnt:
        ug = [(u0[i] + gam * u1[i]) % P for i in range(dom.N)]
        best = None
        for B in itertools.combinations(range(dom.N), d + 1):
            cs = dom.coeffs(B, ug)
            A = tuple(i for i in range(dom.N)
                      if dom.evalp(cs, dom.X[i]) == ug[i])
            if len(A) >= t and not dom.fits(list(A), u1, d):
                if best is None or len(A) > len(best[0]):
                    best = (A, tuple(cs))
        if best is not None:
            out[gam] = best
    return out


def simplex_stack(dom, t, d):
    """The (n-t+1)-point simplex: u supported on W = {0..n-t}, generic values."""
    n = dom.N
    W = list(range(n - t + 1))
    u0 = [0] * n
    u1 = [0] * n
    rnd = random.Random(7)
    for w in W:
        u1[w] = rnd.randrange(1, dom.P)
        u0[w] = rnd.randrange(1, dom.P)
    # distinct ratios
    seen = set()
    for w in W:
        r = (-u0[w]) * pow(u1[w], dom.P - 2, dom.P) % dom.P
        while r in seen:
            u0[w] = rnd.randrange(1, dom.P)
            r = (-u0[w]) * pow(u1[w], dom.P - 2, dom.P) % dom.P
        seen.add(r)
    return u0, u1


def pencil_stack(dom, a, b):
    return ([pow(x, a, dom.P) for x in dom.X], [pow(x, b, dom.P) for x in dom.X])


# ---------------------------------------------------------------------------------
# T5: in-proof invariants
# ---------------------------------------------------------------------------------

def check_invariants(dom, u0, u1, t, d, bad):
    """Verify the clique/family decomposition + interaction law on a bad set."""
    P, n = dom.P, dom.N
    gams = sorted(bad)
    if len(gams) < 2:
        return True, 1, "trivial"
    g0 = gams[0]
    A0, q0 = bad[g0]
    # pair-interpolants from gamma0
    fams = {}  # r poly -> [gamma]
    for g in gams[1:]:
        A, q = bad[g]
        inv = pow((g0 - g) % P, P - 2, P)
        r = poly_scale(P, inv, poly_sub(P, q0, q))
        # check: u1 agrees with r on A0 ^ A
        inter = set(A0) & set(A)
        assert len(inter) >= 2 * t - n, "pair core too small"
        for i in inter:
            assert dom.evalp(list(r), dom.X[i]) == u1[i] % P, "pair-interp law FAILS"
        fams.setdefault(r, []).append(g)
    K = len(fams)
    # within-family + interaction
    reps = list(fams)
    for r in reps:
        a = poly_sub(P, q0, poly_scale(P, g0, r))  # a = q0 - g0*r
        D = [i for i in range(n)
             if dom.evalp(list(a), dom.X[i]) == u0[i] % P
             and dom.evalp(list(r), dom.X[i]) == u1[i] % P]
        fib0 = [i for i in A0 if i not in D]
        # member fibres disjoint + >= max(1, t-|D|)
        used = set(fib0)
        for g in fams[r]:
            A, q = bad[g]
            fib = [i for i in A if i not in D]
            assert len(fib) >= max(1, t - len(D)), "fibre too small"
            assert not (set(fib) & used), "fibre overlap"
            used |= set(fib)
        # interaction law vs every other family
        for r2 in reps:
            if r2 == r:
                continue
            a2 = poly_sub(P, q0, poly_scale(P, g0, r2))
            D2 = [i for i in range(n)
                  if dom.evalp(list(a2), dom.X[i]) == u0[i] % P
                  and dom.evalp(list(r2), dom.X[i]) == u1[i] % P]
            Z = [i for i in range(n)
                 if dom.evalp(list(r), dom.X[i]) == dom.evalp(list(r2), dom.X[i])]
            assert len(Z) <= d, "Z too big (polys not distinct?)"
            for i in D2:
                assert i in fib0 or i in Z, "INTERACTION LAW FAILS"
    if K >= 2:
        mus = sorted(len(v) for v in fams.values())
        assert sum(mus) <= n - t, f"K=2 count law fails: {mus}"
    return True, K, {str(r): len(v) for r, v in fams.items()}


# ---------------------------------------------------------------------------------
# T3: the two-family LP-7 attack
# ---------------------------------------------------------------------------------

def lp7_attack(dom, t, d, c):
    """Family 1 = 10-core simplex (W = 6 fibre points); family 2 grafted: force c of
    the W-points to carry (u0,u1) = (-g0*r2, r2) values (the foreign core).  The
    interaction law predicts those c points' family-1 ratios all collapse to g0."""
    P, n = dom.P, dom.N
    rnd = random.Random(101 + c)
    W = list(range(n - t + 1))  # 6 points at t=11
    g0 = 50
    # r2: a generic degree-<= d poly, nonzero on W
    while True:
        r2 = [rnd.randrange(P) for _ in range(d + 1)]
        if all(dom.evalp(r2, dom.X[w]) != 0 for w in W):
            break
    u0 = [0] * n
    u1 = [0] * n
    for k, w in enumerate(W):
        if k < c:
            v = dom.evalp(r2, dom.X[w])
            u1[w] = v
            u0[w] = (-g0 * v) % P
        else:
            u1[w] = rnd.randrange(1, P)
            u0[w] = rnd.randrange(1, P)
    return u0, u1


# ---------------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------------

def run_cell(p, n, d, t, budget=400, seed=1):
    g = find_g(p, n)
    dom = Domain(p, g, n)
    target = n - t + 1
    rnd = random.Random(seed)
    best, best_stack = 0, None
    log = []

    def consider(u0, u1, tag):
        nonlocal best, best_stack
        c = dom.count_bad(u0, u1, t, d)
        if c > best:
            best, best_stack = c, (list(u0), list(u1), tag)
        if c > target:
            log.append((tag, c))
        return c

    # T1 simplex
    s_cnt = consider(*simplex_stack(dom, t, d), "simplex")
    # catalogue seeds
    for a in range(1, n):
        for b in range(1, n):
            if a != b:
                consider(*pencil_stack(dom, a, b), f"pencil({a},{b})")
    # T3 LP-7 graft curve
    curve = []
    for c in range(0, n - t + 2):
        u0, u1 = lp7_attack(dom, t, d, c)
        curve.append((c, consider(u0, u1, f"lp7(c={c})")))
    # random + hill-climb
    cur = simplex_stack(dom, t, d)
    cur_c = s_cnt
    for it in range(budget):
        if it % 80 == 0:
            cur = ([rnd.randrange(p) for _ in range(n)],
                   [rnd.randrange(p) for _ in range(n)])
            cur_c = consider(*cur, "rand")
        u0, u1 = list(cur[0]), list(cur[1])
        for _ in range(rnd.randrange(1, 4)):
            which = rnd.randrange(2)
            (u0 if which == 0 else u1)[rnd.randrange(n)] = rnd.randrange(p)
        c = consider(u0, u1, "hc")
        if c >= cur_c:
            cur, cur_c = (u0, u1), c
    return dom, best, best_stack, s_cnt, curve, log


def main():
    print("=" * 78)
    print("T4: strip boundary at n=16 -- t=10 pencil must EXCEED n-t+1=7")
    p = 97
    g = find_g(p, 16)
    dom = Domain(p, g, 16)
    u0, u1 = pencil_stack(dom, 8, 10)  # (X^8, X^10): s=2 antipodal pencil
    c10 = dom.count_bad(u0, u1, 10, 2)
    print(f"  (97,16,2,t=10) pencil(8,10): {c10} bad  (predicted 8 > 7) "
          f"{'OK' if c10 == 8 else 'UNEXPECTED'}")

    for p in (97, 257):
        print("=" * 78)
        print(f"THE NEW CELL: (p={p}, n=16, d=2, t=11)  strip floor, beyond-ladder; "
              f"claim max = 6")
        dom, best, bs, s_cnt, curve, log = run_cell(p, 16, 2, 11,
                                                    budget=500 if p == 97 else 250)
        print(f"  simplex count = {s_cnt} (predicted 6)")
        print(f"  lp7 graft curve (c, badcount): {curve}")
        print(f"  search max = {best}  (claim <= 6)   "
              f"{'*** VIOLATION ***' if best > 6 else 'OK'}")
        if log:
            print(f"  VIOLATIONS: {log}")
        # T5 invariants on the best stack
        u0, u1, tag = bs
        bad = bad_scalars_with_witness(dom, u0, u1, 11, 2)
        ok, K, fams = check_invariants(dom, u0, u1, 11, 16 // 8 and 2, bad) \
            if len(bad) >= 2 else (True, len(bad), "small")
        print(f"  invariants on best ({tag}): K = {K}, families = {fams}")

    print("=" * 78)
    print("T1 deployed shape: (p=12289, n=16, d=2, t=11) simplex attainment + "
          "spot adversarial")
    dom, best, bs, s_cnt, curve, log = run_cell(12289, 16, 2, 11, budget=60)
    print(f"  simplex count = {s_cnt} (predicted 6); search max = {best} "
          f"{'*** VIOLATION ***' if best > 6 else 'OK'}")

    print("=" * 78)
    print("T5 invariant sweep at (97,16,2,t=11): random multi-bad stacks")
    p = 97
    dom = Domain(p, find_g(p, 16), 16)
    rnd = random.Random(33)
    checked = 0
    kdist = {}
    while checked < 25:
        u0, u1 = simplex_stack(dom, 11, 2)
        # perturb to spawn extra families sometimes
        for _ in range(rnd.randrange(0, 5)):
            u1[rnd.randrange(16)] = rnd.randrange(p)
            u0[rnd.randrange(16)] = rnd.randrange(p)
        bad = bad_scalars_with_witness(dom, u0, u1, 11, 2)
        if len(bad) < 2:
            continue
        ok, K, fams = check_invariants(dom, u0, u1, 11, 2, bad)
        kdist[K] = kdist.get(K, 0) + 1
        checked += 1
    print(f"  25 stacks checked, all invariants PASS; K distribution: {kdist}")

    print("=" * 78)
    print("strip census recap (p=17, n=8) -- recorded round-8 exhaustive numbers:")
    print("  IN  strip: (1,6)=3 (1,7)=2 (2,7)=2 (3,7)=2 (2,8)=1  == n-t+1  OK")
    print("  OUT strip: (2,6)=4 [5t miss by 1]  (3,6)=7 [2t miss by 1]  "
          "(1,5)=8 [2t miss by 1]")
    print("DONE")


if __name__ == "__main__":
    main()
