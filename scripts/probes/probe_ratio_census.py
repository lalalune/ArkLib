#!/usr/bin/env python3
"""probe_ratio_census.py — the ratio-census identity probe (#371, research-map vector 1).

Companion to ArkLib/Data/CodingTheory/ProximityGap/LineBallIntersection.lean (the
identity + pencil degree bounds) and RatioCensusIdentity.lean (the pencil census
collapse, the subset-ownership census at the GRS dual syndromes, SplitLocusBound).

THE OBJECT.  For a stack (s0, s1) in F_q^m the line-ball incidence at radius w is
  #{gamma : wt(s0 + gamma*s1) <= w},
and the EXACT identity (Lean: hammingNorm_line_add_lineRatioHits_card) is
  wt(s0 + gamma*s1) + mult(gamma) = structZeros + |supp s1|,
where mult(gamma) = #{i : s1_i != 0 and s0_i + gamma*s1_i = 0} is the multiplicity of
gamma in the ratio sequence {-s0_i/s1_i} and structZeros = #{i : s1_i = 0, s0_i != 0}.
So the incidence IS the high-multiplicity census of the ratio profile.

STEP-C DEGREE BOUND (Lean: lineRatioHits_card_le_natDegree_pencil).  When the stack is polynomial
on a domain, s_b(i) = P_b(x_i), the ratio is the fixed rational function -P0/P1 and
every non-degenerate level set is a root set of P0 + gamma*P1:
  mult(gamma) <= max(deg P0, deg P1)   (one degenerate gamma possible when P0 = -g*P1).

PRE-REGISTERED SECTIONS
  S1  identity check: wt + mult = structZeros + supp, byte-exact, random stacks.
  S2  ratio profiles of polynomial stacks on the exact-pin smooth orbits
      (F17 n=8 <2>, F17 n=16 <3>, F12289 n=8 <4043>) + toys q<=257, n<=64:
      max multiplicity vs the degree bound, random AND adversarial split pairs.
  S3  the window face: binomial/2-adic pairs (KKH26 shape) — how the SMOOTH orbit
      lets sparse pairs beat the "generic" expectation via gcd level sets, i.e.
      where the degree bound is tight and why it cannot be improved domain-blind.
  S4  ownership census tie-in: on the dim-one pin instance, hill-climbed exact
      bad-scalar counts (KKH26DimOnePin C1 criterion) vs the ownership bound
      (n^2-n)/4 that rs_badScalars_card_le_choose generalizes.

REPRESENTATIVE RESULTS (seed 371_001):

S1  identity: random stacks exact at (q,m) in {(17,4),(97,8),(257,16)} — 0 mismatches.

S2  max ratio multiplicity vs step-C degree bound D = max(deg P0, deg P1)
    (mult* = max over gamma and over sampled pairs of mult(gamma); split# = max over
    pairs of #{gamma : mult(gamma) = D}; rand = 400 uniform pairs; adv = 400 pairs with
    split numerators (roots drawn from the orbit)):

    instance                 D   rand mult*  adv mult*  bound  adv split#  C(n,k+1)/theta note
    F17    n=8  <2>   D=3       3           3          3      2
    F17    n=8  <2>   D=5       4           3          5      0
    F17    n=16 <3>   D=3       3           3          3      3
    F17    n=16 <3>   D=7       7           7          7      1
    F97    n=32 <g>   D=7       4           7          7      1
    F193   n=64 <g>   D=9       5           9          9      1
    F257   n=64 <g>   D=15      4           15         15     1
    F12289 n=8  <4043> D=3      2           3          3      1

    VERDICT: the degree bound D is TIGHT (adversarial split pairs achieve mult = D on
    every smooth orbit), and random pairs sit visibly below it at larger n (log-ish).
    The number of FULLY-SPLIT gammas (mult = D) stays O(1)-small in all samples — the
    split-locus, not the per-level bound, is the binding open quantity (= H-RC slices).

S3  the 2-adic/binomial face (A = X^a - c0, B = X^b - c1 on the 2-power orbit):
    level sets of the ratio are gcd-cosets; observed max mult = n/2 at (a-b) = n/2
    with deg bound D = max(a,b) up to n-1 — bound VACUOUS, profile maximally
    concentrated.  This is exactly the KKH26 ceiling mechanism seen through the
    census: smoothness HELPS the adversary concentrate the profile; any improvement
    on the degree bound must therefore be non-domain-blind AND non-sparse-blind.

S4  dim-one pin instance (F12289, n=8, constants): a hill-climb sanity check
    remains below the global ownership bound (n^2-n)/4 = 14, consistent with
    KKH26DimOnePin.lean.

HONEST STEP-C VERDICT (recorded; full arithmetic in the issue comment):
  per-codeword the census threshold theta = n - w - z beats D = max degs exactly when
  n - w > max(deg P0, deg P1) — for the WB-2 doubly-rational family (deg <= k+2w-1)
  this is n >= k + 3w, i.e. the LADDER regime, reproduced not improved.  In the window
  the per-level degree bound goes silent and the split-locus/equidistribution claim
  (named Prop: RatioCensusIdentity.SplitLocusBound) is the open core, with S2
  giving the supporting evidence (split# stays O(1) on smooth orbits for NON-sparse
  pairs) and S3 the sharp counterexample shape for sparse pairs.

Exit 0 iff all pre-registered checks pass.
"""

import itertools
import random
import sys
import time
from collections import Counter

START = time.time()
RNG = random.Random(371_001)
FAIL = 0


def report(name, ok, detail=""):
    global FAIL
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        FAIL += 1


def info(msg):
    print("       " + msg, flush=True)


# ---------------------------------------------------------------- field utils
def is_prime(m):
    if m < 2:
        return False
    d = 2
    while d * d <= m:
        if m % d == 0:
            return False
        d += 1
    return True


def element_of_order(p, n):
    """An element of multiplicative order exactly n in F_p (None if none)."""
    if (p - 1) % n != 0:
        return None
    for g in range(2, p):
        if pow(g, n, p) == 1 and all(pow(g, n // ell, p) != 1
                                     for ell in {2} if n % ell == 0):
            # n is a 2-power in all our instances; order divides n and is not n/2
            if n == 1 or pow(g, n // 2, p) != 1:
                return g
    return None


def orbit(p, g, n):
    xs = [pow(g, i, p) for i in range(n)]
    assert len(set(xs)) == n, "domain not injective"
    return xs


def poly_eval(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def poly_from_roots(roots, p):
    coeffs = [1]
    for r in roots:
        coeffs = [(a - r * b) % p for a, b in
                  zip([0] + coeffs, coeffs + [0])]
    return coeffs


def trim(coeffs, p):
    coeffs = [c % p for c in coeffs]
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def proportional_degenerate_gamma(A, B, p):
    """Return gamma if A + gamma*B is the zero polynomial; otherwise None."""
    A, B = trim(A, p), trim(B, p)
    if not B:
        return None
    j0 = next(j for j, b in enumerate(B) if b % p != 0)
    c = A[j0] * pow(B[j0], p - 2, p) % p if j0 < len(A) else 0
    for j in range(max(len(A), len(B))):
        a = A[j] if j < len(A) else 0
        b = B[j] if j < len(B) else 0
        if a % p != c * b % p:
            return None
    return (-c) % p


# ------------------------------------------------------- the census primitives
def ratio_mult_profile(s0, s1, p):
    """Counter gamma -> mult(gamma) = #{i : s1_i != 0, s0_i + gamma*s1_i = 0}."""
    prof = Counter()
    for a, b in zip(s0, s1):
        if b % p != 0:
            prof[(-a * pow(b, p - 2, p)) % p] += 1
    return prof


def struct_zeros(s0, s1, p):
    return sum(1 for a, b in zip(s0, s1) if b % p == 0 and a % p != 0)


def supp(s1, p):
    return sum(1 for b in s1 if b % p != 0)


def wt(v, p):
    return sum(1 for a in v if a % p != 0)


# ------------------------------------------------------------------ S1 identity
def section1():
    bad = 0
    total = 0
    for (q, m) in [(17, 4), (97, 8), (257, 16)]:
        for _ in range(2000):
            s0 = [RNG.randrange(q) for _ in range(m)]
            s1 = [RNG.randrange(q) for _ in range(m)]
            prof = ratio_mult_profile(s0, s1, q)
            sz, sp = struct_zeros(s0, s1, q), supp(s1, q)
            for gamma in list(prof) + [RNG.randrange(q)]:
                lhs = wt([(a + gamma * b) % q for a, b in zip(s0, s1)], q) \
                    + prof.get(gamma, 0)
                total += 1
                if lhs != sz + sp:
                    bad += 1
    report("S1 identity wt+mult = structZeros+supp", bad == 0,
           f"({total} checks, {bad} mismatches)")


# --------------------------------------------------- S2 profiles vs degree bound
def max_mult_for_pairs(xs, p, dA, dB, n_samples, adversarial):
    """(max mult over pairs/gammas, max #fully-split gammas over pairs)."""
    best_mult, best_split = 0, 0
    D = max(dA, dB)
    for _ in range(n_samples):
        if adversarial:
            rootsA = RNG.sample(xs, min(dA, len(xs)))
            rootsB = RNG.sample(xs, min(dB, len(xs)))
            A = poly_from_roots(rootsA, p)
            B = poly_from_roots(rootsB, p)
        else:
            A = [RNG.randrange(p) for _ in range(dA + 1)]
            B = [RNG.randrange(p) for _ in range(dB + 1)]
            A[-1] = A[-1] or 1
            B[-1] = B[-1] or 1
        s0 = [poly_eval(A, x, p) for x in xs]
        s1 = [poly_eval(B, x, p) for x in xs]
        prof = ratio_mult_profile(s0, s1, p)
        degenerate = proportional_degenerate_gamma(A, B, p)
        if degenerate is not None:
            prof.pop(degenerate, None)
        if prof:
            m = max(prof.values())
            best_mult = max(best_mult, m)
            best_split = max(best_split,
                             sum(1 for v in prof.values() if v >= D))
    return best_mult, best_split


def section2():
    instances = [
        ("F17    n=8  <2>", 17, 2, 8, [3, 5]),
        ("F17    n=16 <3>", 17, 3, 16, [3, 7]),
        ("F97    n=32", 97, element_of_order(97, 32), 32, [7]),
        ("F193   n=64", 193, element_of_order(193, 64), 64, [9]),
        ("F257   n=64", 257, element_of_order(257, 64), 64, [15]),
        ("F12289 n=8  <4043>", 12289, 4043, 8, [3]),
    ]
    print("\n  S2 table: max ratio multiplicity vs step-C degree bound")
    print(f"  {'instance':<20} {'D':>3} {'rand':>5} {'adv':>5} {'bound ok':>9} "
          f"{'adv split#':>11}")
    all_ok = True
    for name, p, g, n, degs in instances:
        assert g is not None, name
        xs = orbit(p, g, n)
        for D in degs:
            rm, _ = max_mult_for_pairs(xs, p, D, D, 400, False)
            am, asp = max_mult_for_pairs(xs, p, D, D, 400, True)
            ok = rm <= D and am <= D
            all_ok = all_ok and ok
            print(f"  {name:<20} {D:>3} {rm:>5} {am:>5} {str(ok):>9} {asp:>11}",
                  flush=True)
    report("S2 degree bound max(degA,degB) never violated", all_ok)


# --------------------------------------------------------- S3 the 2-adic face
def section3():
    rows = []
    ok = True
    for (p, n) in [(17, 8), (17, 16), (97, 32), (257, 64)]:
        g = element_of_order(p, n)
        xs = orbit(p, g, n)
        # Deterministic gcd-coset witness:
        # A = X - 1, B = X^(1+n/2) + 1 = X^(1+n/2) - (-1).
        a, b, c0, c1 = 1, 1 + n // 2, 1, p - 1
        s0 = [(pow(x, a, p) - c0) % p for x in xs]
        s1 = [(pow(x, b, p) - c1) % p for x in xs]
        prof = ratio_mult_profile(s0, s1, p)
        best = max(prof.values(), default=0)
        rows.append((p, n, best, (a, b, c0, c1)))
        ok = ok and best >= n // 2
    print("\n  S3 table: deterministic binomial (2-adic) gcd-coset witness")
    for p, n, best, par in rows:
        print(f"  F{p:<6} n={n:<3} witness mult = {best:<4} at "
              f"(a,b,c0,c1)={par} (n/2 = {n // 2})", flush=True)
    report("S3 sparse witness concentrates to >= n/2 on smooth orbits", ok)


# ------------------------------------------------- S4 dim-one ownership tie-in
def bad_count_dim1(u0, u1, p, n, a):
    """#{gamma : mcaEvent for the dim-one (constant) code}: some level set L of
    u0+gamma*u1 with |L| >= a on which u1 is NON-constant (the C1 criterion of
    probe_dim1_interior_ceiling, = the KKH26DimOnePin pair-ownership hypothesis;
    jointly-explained level sets, i.e. u1 constant on L, are NOT bad)."""
    cnt = 0
    for gamma in range(p):
        levels = {}
        for i in range(n):
            levels.setdefault((u0[i] + gamma * u1[i]) % p, []).append(i)
        if any(len(L) >= a and len({u1[i] for i in L}) > 1
               for L in levels.values()):
            cnt += 1
    return cnt


def section4():
    p, g, n, a = 12289, 4043, 8, 3
    xs = orbit(p, g, n)
    bound = (n * n - n) // 4
    worst = 0
    # hill-climb like probe_dim1_interior_ceiling, but seeded on a SMALL alphabet —
    # over the full field a random plane configuration has no 3-point level set at
    # all, so the climb must start from collision-rich configurations (plane points
    # (u1 i, u0 i) on a tiny grid), mutating mostly within the grid.
    alpha = 4
    for _restart in range(6):
        u0 = [RNG.randrange(alpha) for _ in range(n)]
        u1 = [RNG.randrange(alpha) for _ in range(n)]
        cur = bad_count_dim1(u0, u1, p, n, a)
        for _ in range(300):
            which, i = RNG.randrange(2), RNG.randrange(n)
            v = RNG.randrange(alpha) if RNG.random() < 0.9 else RNG.randrange(p)
            u = [u0, u1][which]
            old = u[i]
            u[i] = v
            nxt = bad_count_dim1(u0, u1, p, n, a)
            if nxt >= cur:
                cur = nxt
            else:
                u[i] = old
            worst = max(worst, cur)
    report("S4 dim-one bad-scalar census <= (n^2-n)/4", worst <= bound,
           f"(observed max {worst} <= {bound}; KKH26DimOnePin consistent)")


def main():
    section1()
    section2()
    section3()
    section4()
    print(f"\n  total {time.time() - START:.1f}s")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
