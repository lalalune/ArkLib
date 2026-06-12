#!/usr/bin/env python3
"""Pre-registered probe: the ALL-WITNESS OWNERSHIP FLOOR (#371).

Claim under test (the lane claim, before any Lean is written):

  For any function u on a w-set S of smooth-domain points with NO degree-<=d fit on S,
  the number of (d+2)-subsets T of S on which u IS degree-d-fit is <= C(w-1, d+2);
  equivalently the unfit (d+2)-subsets (the owned, gamma-determining ones) number
  >= C(w-1, d+1).

Pre-registered sections (any FAIL refutes the floor and goes to DISPROOF_LOG):
  A. Exhaustive floor check at p=13 (n=12 smooth domain), d in {0,1,2},
     w in {d+2..7}: ALL u over small value alphabets, plus random u over full field.
  B. Tightness: single-deviation stacks attain the floor exactly: unfit count
     == C(w-1, d+1) (so the floor cannot be improved).
  C. Adversarial minimization at p=17 (n=16), d in {1,2,3}, w up to 10:
     hill-climb to MINIMIZE the unfit-subset count; record min vs C(w-1,d+1).
  D. The divided-difference recursion invariants used by the Lean proof:
     (i)  for w >= d+3 there is x* in S with S-minus-x* unfit;
     (ii) for x* in S, G subset of S-minus-x*: fit(d, G+{x*}, u) <=>
          fit(d-1, G, v) with v(i) = (u(i)-u(x*))/(x_i - x_{x*})  (d >= 1).

Exact arithmetic mod p throughout.  Exit 0 iff every section passes.
"""

import itertools
import random
import sys

random.seed(371_2026)


def inv(a, p):
    return pow(a, p - 2, p)


def fits_deg(points, vals, d, p):
    """Is there a poly of degree <= d through (points[i], vals[i])? (distinct points)"""
    m = len(points)
    if m <= d + 1:
        return True
    # Lagrange-interpolate on the first d+1 points, then test the rest.
    base = points[: d + 1]
    bv = vals[: d + 1]

    def interp_at(x):
        tot = 0
        for j in range(d + 1):
            num, den = 1, 1
            for k in range(d + 1):
                if k != j:
                    num = num * ((x - base[k]) % p) % p
                    den = den * ((base[j] - base[k]) % p) % p
            tot = (tot + bv[j] * num * inv(den, p)) % p
        return tot

    return all(interp_at(points[i]) == vals[i] % p for i in range(d + 1, m))


def unfit_subset_count(dom, u, S, d, p):
    """(#unfit, #fit) over (d+2)-subsets of S; u is a dict index->value."""
    unfit = fit = 0
    for T in itertools.combinations(S, d + 2):
        pts = [dom[i] for i in T]
        vs = [u[i] for i in T]
        if fits_deg(pts, vs, d, p):
            fit += 1
        else:
            unfit += 1
    return unfit, fit


def comb(n, k):
    if k < 0 or k > n:
        return 0
    from math import comb as c

    return c(n, k)


def smooth_domain(p, n):
    # find generator of the order-n subgroup of F_p^*
    for g in range(2, p):
        if pow(g, n, p) == 1 and all(pow(g, n // q, p) != 1 for q in {2, 3} if n % q == 0):
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element")


failures = []


def check(name, cond, detail=""):
    if not cond:
        failures.append((name, detail))
        print(f"  FAIL {name} {detail}")


# ---------------- Section A: exhaustive + random floor check ----------------
print("Section A: floor check, p=13")
p = 13
n = 12
dom = smooth_domain(p, n)
for d in (0, 1, 2):
    for w in range(d + 2, 8):
        S = list(range(w))  # first w domain indices
        floor = comb(w - 1, d + 1)
        cap_fit = comb(w - 1, d + 2)
        # exhaustive over alphabet {0,1,2} (captures all the combinatorics of fits
        # for small d), plus 400 random full-field u
        cases = []
        if 3**w <= 30000:
            cases += [dict(zip(S, vals)) for vals in itertools.product(range(3), repeat=w)]
        cases += [{i: random.randrange(p) for i in S} for _ in range(400)]
        worst = None
        for u in cases:
            pts = [dom[i] for i in S]
            vs = [u[i] for i in S]
            if fits_deg(pts, vs, d, p):
                continue  # not a witness configuration
            unfit, fit = unfit_subset_count(dom, u, S, d, p)
            if worst is None or unfit < worst:
                worst = unfit
            check(
                f"A d={d} w={w}",
                unfit >= floor and fit <= cap_fit,
                f"unfit={unfit} floor={floor} fit={fit} cap={cap_fit}",
            )
        print(f"  d={d} w={w}: min unfit observed={worst} floor={floor}  OK")

# ---------------- Section B: deviation stacks attain the floor ----------------
print("Section B: tightness at deviation stacks, p=13")
for d in (0, 1, 2):
    for w in range(d + 3, 9):
        S = list(range(w))
        # u = polynomial of degree <= d on S minus last point, deviates there
        coeffs = [random.randrange(p) for _ in range(d + 1)]

        def ev(x):
            t = 0
            for c in reversed(coeffs):
                t = (t * x + c) % p
            return t

        u = {i: ev(dom[i]) for i in S}
        u[S[-1]] = (u[S[-1]] + 1 + random.randrange(p - 1)) % p
        pts = [dom[i] for i in S]
        vs = [u[i] for i in S]
        assert not fits_deg(pts, vs, d, p)
        unfit, fit = unfit_subset_count(dom, u, S, d, p)
        floor = comb(w - 1, d + 1)
        check(f"B d={d} w={w}", unfit == floor, f"unfit={unfit} floor={floor}")
        print(f"  d={d} w={w}: deviation unfit={unfit} == C({w - 1},{d + 1})={floor}  OK")

# ---------------- Section C: adversarial minimization ----------------
print("Section C: adversarial minimization, p=17")
p = 17
n = 16
dom = smooth_domain(p, n)
for d in (1, 2, 3):
    for w in (d + 3, d + 5, min(10, n)):
        if w > n:
            continue
        S = list(range(w))
        floor = comb(w - 1, d + 1)
        best = None
        for trial in range(60):
            u = {i: random.randrange(p) for i in S}
            pts = [dom[i] for i in S]
            if fits_deg(pts, [u[i] for i in S], d, p):
                continue
            cur, _ = unfit_subset_count(dom, u, S, d, p)
            improved = True
            while improved:
                improved = False
                for i in S:
                    old = u[i]
                    for v2 in range(p):
                        if v2 == old:
                            continue
                        u[i] = v2
                        if fits_deg(pts, [u[j] for j in S], d, p):
                            continue
                        c2, _ = unfit_subset_count(dom, u, S, d, p)
                        if c2 < cur:
                            cur = c2
                            improved = True
                            old = v2
                    u[i] = old
            if best is None or cur < best:
                best = cur
        check(f"C d={d} w={w}", best is not None and best >= floor, f"min={best} floor={floor}")
        print(f"  d={d} w={w}: hill-climbed min unfit={best} floor={floor}  OK")

# ---------------- Section D: the recursion invariants ----------------
print("Section D: divided-difference recursion invariants, p=13")
p = 13
n = 12
dom = smooth_domain(p, n)
for d in (1, 2):
    for w in range(d + 3, 8):
        S = list(range(w))
        for _ in range(300):
            u = {i: random.randrange(p) for i in S}
            pts = [dom[i] for i in S]
            if fits_deg(pts, [u[i] for i in S], d, p):
                continue
            # (i) some erasure stays unfit
            ok = any(
                not fits_deg(
                    [dom[i] for i in S if i != x],
                    [u[i] for i in S if i != x],
                    d,
                    p,
                )
                for x in S
            )
            check(f"D(i) d={d} w={w}", ok, "all erasures fit")
            # (ii) the divided-difference equivalence at a random x*
            xs = random.choice(S)
            a = dom[xs]
            v = {
                i: (u[i] - u[xs]) * inv((dom[i] - a) % p, p) % p
                for i in S
                if i != xs
            }
            rest = [i for i in S if i != xs]
            for G in itertools.combinations(rest, d + 1):
                lhs = fits_deg(
                    [dom[i] for i in G] + [a], [u[i] for i in G] + [u[xs]], d, p
                )
                rhs = fits_deg([dom[i] for i in G], [v[i] for i in G], d - 1, p)
                check(f"D(ii) d={d} w={w}", lhs == rhs, f"G={G} lhs={lhs} rhs={rhs}")
print("  D: all invariant checks passed" if not failures else "  D: failures above")

print()
if failures:
    print(f"PROBE FAILED: {len(failures)} failures")
    sys.exit(1)
print("ALL SECTIONS PASS — the all-witness floor, tightness, and recursion invariants hold")
sys.exit(0)
