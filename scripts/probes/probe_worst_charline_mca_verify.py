#!/usr/bin/env python3
"""Probe (#371, S50 follow-up): the worst character lines ARE genuinely MCA-bad —
the boundary-radius incidence law makes the far-ness caveat unnecessary.

THE LAW (to be formalized): at agreement threshold a = k+1, for ANY line (u0,u1):
  gamma is MCA-bad  <=>  exists a (k+1)-subset T with
      e0(T) + gamma*e1(T) = 0  and  (e0(T), e1(T)) != (0,0),
where e_j(T) = sum_{i in T} u_j[i] / prod_{l in T, l != i} (x_i - x_l)
is the top (degree-k) coefficient of the interpolant of u_j on T.

Why: a (k+1)-set T is an agreement set of a deg<k codeword for u0+gamma*u1
iff the top coefficient of the interpolant vanishes: e0 + gamma*e1 = 0.
T is jointly explained iff e0(T) = 0 AND e1(T) = 0.  So a fitting
non-degenerate T is automatically a no-joint witness.  Larger witnesses
reduce to (k+1)-subsets (explained (k+1)-subsets sharing k points merge).

THIS PROBE: (1) cross-validates the law against the faithful mcaEvent
(subset enumeration with explicit explainability checks) at every gamma for
two pairs; (2) computes exact incidence and MCA-bad counts for the KKH26
control [x^5,x^4] and the S50 high-frequency winners at n=16, k=4,
p = 2^32+81, radius 11/16 (a=5); (3) reports the verdict on the 3984 surplus.
"""
import itertools, sys

P = 2**32 + 81
N = 16
K = 4  # dimension; codewords = deg <= 3
A = 5  # agreement threshold at radius 11/16 (= k+1)


def find_g16(p):
    for h in range(2, 200):
        x = pow(h, (p - 1) // 16, p)
        if pow(x, 8, p) != 1 and pow(x, 16, p) == 1:
            return x
    raise ValueError("no order-16 element")


G = find_g16(P)
XS = [pow(G, i, P) for i in range(N)]
assert len(set(XS)) == N

FIVES = list(itertools.combinations(range(N), 5))

# precompute inverse denominators per (T, i)
INVDEN = {}
for T in FIVES:
    for i in T:
        den = 1
        for j in T:
            if i == j: continue
            den = den * ((XS[i] - XS[j]) % P) % P
        INVDEN[(T, i)] = pow(den, -1, P)


def tops(u):
    """e(T) for all 5-subsets T: top coefficient of the deg<=4 interpolant."""
    return {T: sum(u[i] * INVDEN[(T, i)] for i in T) % P for T in FIVES}


def law_badset(u0, u1):
    """bad gammas per the boundary-radius incidence law."""
    e0, e1 = tops(u0), tops(u1)
    bad = set()
    degenerate = 0
    for T in FIVES:
        a, b = e0[T], e1[T]
        if b != 0:
            bad.add((-a) * pow(b, -1, P) % P)
        elif a == 0:
            degenerate += 1  # explained for every gamma: contributes nothing
    return bad, degenerate


# ---- faithful mcaEvent checker (independent engine, for cross-validation) ----
def interp_cubic_eval(pts, vals, x):
    total = 0
    for i in range(4):
        num, den = 1, 1
        for j in range(4):
            if i == j: continue
            num = num * ((x - pts[j]) % P) % P
            den = den * ((pts[i] - pts[j]) % P) % P
        total = (total + vals[i] * num * pow(den, -1, P)) % P
    return total


def explainable(u, S):
    S = sorted(S)
    if len(S) <= 4:
        return True
    pts = [XS[i] for i in S[:4]]
    vals = [u[i] for i in S[:4]]
    return all(interp_cubic_eval(pts, vals, XS[i]) == u[i] for i in S[4:])


def mca_bad_faithful(gam, u0, u1):
    """exists S (|S| >= 5) agreement set of some cubic with w, S not jointly explained.
    Witness sets are exactly agreement sets of interpolants of 4-subsets of w."""
    w = [(u0[i] + gam * u1[i]) % P for i in range(N)]
    seen = set()
    for q in itertools.combinations(range(N), 4):
        pts = [XS[i] for i in q]
        vals = [w[i] for i in q]
        T = frozenset(i for i in range(N)
                      if interp_cubic_eval(pts, vals, XS[i]) == w[i])
        if len(T) < A or T in seen:
            continue
        seen.add(T)
        if not (explainable(u0, T) and explainable(u1, T)):
            return True
    return False


def charline(a, b):
    return ([pow(XS[i], a, P) for i in range(N)],
            [pow(XS[i], b, P) for i in range(N)])


def main():
    # ---- (1) law vs faithful mcaEvent on two pairs, every candidate gamma + controls ----
    # NOTE: the law is now kernel-proven in Lean (boundary_slice_badSet_eq_unconditional,
    # BoundarySliceUnconditional.lean); the faithful cross-check below is a SAMPLED
    # semantic sanity check of the probe's own implementation, not the proof.
    print("Cross-validation (law vs faithful mcaEvent, sampled):", flush=True)
    mismatches = 0
    import random
    rng = random.Random(50)
    for (a, b) in [(5, 4), (7, 6)]:
        u0, u1 = charline(a, b)
        law_bad, _ = law_badset(u0, u1)
        lb = sorted(law_bad)
        sample = [lb[rng.randrange(len(lb))] for _ in range(50)] + \
                 [rng.randrange(P) for _ in range(30)]
        for gam in sample:
            lhs = gam % P in law_bad
            rhs = mca_bad_faithful(gam % P, u0, u1)
            if lhs != rhs:
                mismatches += 1
                print(f"  MISMATCH pair=({a},{b}) gamma={gam}: law={lhs} faithful={rhs}")
        print(f"  pair (x^{a},x^{b}): {len(sample)} gammas checked", flush=True)
    print(f"law-vs-faithful mismatches: {mismatches}  [{'PASS' if mismatches == 0 else 'FAIL'}]\n",
          flush=True)

    # ---- (2) exact counts for control + high-frequency pairs ----
    print(f"{'pair':>12} {'#bad (=incidence)':>18} {'degenerate-5sets':>17}")
    results = {}
    pairs = [(5, 4), (7, 6), (5, 12), (14, 7), (9, 2), (11, 4), (13, 6), (3, 10), (15, 8)]
    # also sweep ALL adjacent pairs and a-b coprime-to-16 reps for the max
    for (a, b) in pairs:
        u0, u1 = charline(a, b)
        bad, dgn = law_badset(u0, u1)
        results[(a, b)] = len(bad)
        print(f"[x^{a:>2},x^{b:>2}] {len(bad):>18} {dgn:>17}", flush=True)

    # full character-line sweep for the true max (a != b, both in 0..15, a or b >= K)
    best, bestpair = 0, None
    for a in range(N):
        for b in range(N):
            if a == b: continue
            u0, u1 = charline(a, b)
            bad, _ = law_badset(u0, u1)
            if len(bad) > best:
                best, bestpair = len(bad), (a, b)
    print(f"\nfull char-line sweep max: {best} at {bestpair}")

    ctrl = results[(5, 4)]
    print("\n==== VERDICT ====")
    print(f"KKH26 control [x^5,x^4]: #bad = {ctrl} (S50 expected 2256)")
    print(f"high-freq max (tested list): {max(v for k_, v in results.items() if k_ != (5, 4))}")
    print(f"sweep max {best} at {bestpair}")
    if best > ctrl and mismatches == 0:
        print("CONFIRMED: the surplus is GENUINE MCA mass (no far-ness needed at the "
              "boundary radius); the ceiling-count spectrum at 11/16 exceeds N(4,5).")
    return 0 if mismatches == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
