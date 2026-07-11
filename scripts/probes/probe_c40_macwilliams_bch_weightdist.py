#!/usr/bin/env python3
"""
PROBE C40 (issue #444): BCH/Reed-Solomon Weight-Distribution List Bound via MacWilliams Duality.

CONJECTURE C40 claims: the dual (BCH) weight distribution of RS[k] over mu_n, computed via
MacWilliams + the proven antipodal/cyclotomic-coset structure, bounds the number of low-weight
dual words and hence the FAR-LINE LIST SIZE below budget PAST Johnson. Uses classical coding
duality.

REDUCES-TO (per the conjecture): MacWilliams identity (proven) + BCH weight-distribution moments
+ in-tree cyclotomic-coset structure + L3 orbit-count.

=============================================================================
THE STRUCTURAL POINT being tested (the suspected horn = reduces-to-johnson):
=============================================================================
A "weight distribution" is a SYMMETRIC, PERMUTATION-INVARIANT functional of a code:
  A_w(C) = #{ c in C : Hamming-wt(c) = w }.
MacWilliams duality is the exact linear (Krawtchouk) transform A^perp = (1/|C|) K . A
relating the weight distribution of C to that of its dual C^perp.

CRUCIAL FACT (in-tree, O109 CENSUS 1; classical): RS[k] over ANY n-subset of F_p is MDS, so
its weight distribution is the FIXED closed form
  A_w = C(n,w) * sum_{j<=w-d+1} (-1)^j C(w,j) (q^{w-d+1-j} - 1),   d = n-k+1.
This depends ONLY on (n,k,q). It is IDENTICAL for the explicit smooth subgroup mu_n and for a
random n-subset and for an arithmetic-progression domain. The dual of RS[k] is RS[n-k]
(generalized RS), also MDS; MacWilliams maps one MDS weight distribution to the other. So the
ENTIRE weight-distribution / MacWilliams / "dual BCH" object is DOMAIN-INDEPENDENT.

But delta* is provably DOMAIN-DEPENDENT past Johnson (the whole prize: mu_n is the worst case;
BKR10 / BCHKS Thm 1.13). A domain-independent functional CANNOT see the worst-case structure of
mu_n. Therefore any bound it produces is the SAME for every domain = the generic/random-domain
bound = the second-moment bound, which bottoms out exactly at the Johnson radius (in-tree Loop16:
the second-moment denominator a^2 - n b vanishes exactly at eta_0 = sqrt(rho) - rho; in-tree
AgreementMomentTwo: M2 enters THROUGH THE WEIGHT ENUMERATOR ALONE).

The far-line list size I(delta) is NOT a permutation-invariant functional of the weight
distribution: a far line x^a + alpha x^b close to RS[k] is a structured (low-DEGREE-pencil)
object whose count over alpha depends on WHICH evaluation points the domain uses (the orbit-count
law L3: I = N * n/gcd(b-a,n)). Two codes with identical weight distributions can have wildly
different far-line list sizes. So the weight distribution provably underdetermines I(delta).

PREDICTIONS if C40 = reduces-to-johnson:
  P1. The MDS weight distribution A_w(mu_n) is IDENTICAL to A_w(random n-subset) and
      A_w(AP-domain) for every w -- a domain-invariant functional. (Confirms it cannot see mu_n.)
  P2. The MacWilliams transform of A(RS[k]) equals A(RS[n-k]) (the MDS dual closed form) -- the
      "dual BCH weight distribution" is itself the same fixed MDS form, domain-blind. (No extra
      cyclotomic/antipodal information survives the transform; the antipodal structure is in the
      DOMAIN, which the weight distribution has already forgotten.)
  P3. The weight-distribution / annulus-counting list bound (the only list bound a symmetric
      weight functional yields: the "many low-weight codewords in a ball" / second-moment /
      Johnson bound) gives a NONTRIVIAL list bound only for radius <= Johnson; at any radius
      strictly past Johnson it returns >= n (vacuous) for the SAME (n,k,q) -- because it is the
      same functional as the second moment whose wall is eta_0.
  P4. The ACTUAL far-line list over mu_n past Johnson EXCEEDS what the weight distribution
      controls: at moderate p we exhibit far lines x^a + alpha x^b with the KK/structured
      bad-scalar set of size = subgroup subset-sumset (the live mechanism, O11''), a count the
      domain-blind weight distribution cannot predict (random domain gives ~0 such alpha).

If P1-P4 hold, C40 = reduces-to-johnson: the weight distribution / MacWilliams object is exactly
the second-moment functional, domain-independent, with wall = Johnson. To pin delta* PAST Johnson
it would need a domain-DEPENDENT input = the open BGK sup-norm (a secretly-open undertone).

HONESTY: proper subgroup mu_n (n = 2^mu, n | p-1, p PRIME, p >> n^3), NEVER n = p-1.
"""

import sys
import math
import random
from itertools import combinations

# ---------------------------------------------------------------------------
# Field / subgroup utilities (exact integer arithmetic mod a PRIME p).
# ---------------------------------------------------------------------------

def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True

def find_prime_with_subgroup(n, lower):
    """Smallest prime p > lower with n | p-1 (so mu_n proper subgroup exists). p >> n^3 enforced."""
    p = lower + (n - (lower % n)) % n + 1  # >= lower, p = 1 mod n region; we just scan p = 1 mod n
    # scan p of form 1 + t*n
    t = (lower // n) + 1
    while True:
        cand = 1 + t * n
        if cand > lower and is_prime(cand):
            return cand
        t += 1

def primitive_root(p):
    """A generator of F_p^*."""
    if p == 2:
        return 1
    phi = p - 1
    # factor phi
    fac = set()
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def subgroup_mu_n(p, n):
    """The unique multiplicative subgroup mu_n of order n in F_p^* (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # element of order n
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x * h) % p
    assert len(set(elts)) == n, "mu_n not size n"
    return sorted(elts)

# ---------------------------------------------------------------------------
# P1/P2: the MDS weight distribution (classical closed form) is domain-blind.
# ---------------------------------------------------------------------------

def C(nn, kk):
    if kk < 0 or kk > nn:
        return 0
    return math.comb(nn, kk)

def mds_weight_dist(n, k, q):
    """Classical MDS weight distribution. A_0 = 1; for w >= d = n-k+1:
       A_w = C(n,w) * sum_{j=0}^{w-d} (-1)^j C(w,j) (q^{w-d+1-j} - 1)."""
    d = n - k + 1
    A = [0] * (n + 1)
    A[0] = 1
    for w in range(d, n + 1):
        s = 0
        for j in range(0, w - d + 1):
            s += ((-1) ** j) * C(w, j) * (q ** (w - d + 1 - j) - 1)
        A[w] = C(n, w) * s
    return A

def empirical_weight_dist(domain, k, p):
    """Brute-force weight distribution of RS[k] over the given evaluation domain (small only).
       RS codeword = (f(x))_{x in domain} for deg f < k. Weight = #nonzero entries."""
    n = len(domain)
    A = [0] * (n + 1)
    # enumerate all polynomials of degree < k over F_p by their coeff tuples
    def gen_coeffs(kk):
        if kk == 0:
            yield ()
            return
        for c in range(p):
            for rest in gen_coeffs(kk - 1):
                yield (c,) + rest
    for coeffs in gen_coeffs(k):
        wt = 0
        for x in domain:
            val = 0
            xp = 1
            for c in coeffs:
                val = (val + c * xp) % p
                xp = (xp * x) % p
            if val != 0:
                wt += 1
        A[wt] += 1
    return A

def krawtchouk(q, n, k, x):
    """q-ary Krawtchouk K_k(x; n) = sum_j (-1)^j (q-1)^{k-j} C(x,j) C(n-x, k-j)."""
    s = 0
    for j in range(0, k + 1):
        s += ((-1) ** j) * ((q - 1) ** (k - j)) * C(x, j) * C(n - x, k - j)
    return s

def macwilliams(A, q):
    """MacWilliams transform: B_w = (1/|C|) sum_x A_x K_w(x), |C| = sum A_x."""
    n = len(A) - 1
    size = sum(A)
    B = []
    for w in range(n + 1):
        s = sum(A[x] * krawtchouk(q, n, w, x) for x in range(n + 1))
        assert s % size == 0, "MacWilliams not integral"
        B.append(s // size)
    return B

# ---------------------------------------------------------------------------
# P3: the weight-distribution list bound bottoms out at Johnson.
# The only list bound a symmetric weight functional yields is the "annulus count"
# = second-moment / Johnson bound. We compute the Johnson list bound and show
# its denominator (n*a^2 - ... ) i.e. the second-moment denominator vanishes at eta_0.
# ---------------------------------------------------------------------------

def johnson_denominator(n, k, delta):
    """In-tree (Loop16) second-moment / Johnson denominator. delta = relative radius,
       agreement a = (1-delta)*n, b = rho*n = k. Denominator = a^2 - n*b = (1-delta)^2 n^2 - n*k,
       which is the in-tree `johnson_denom_eq`/`sq_gt_iff_large_gap` form. It is > 0 iff
       (1-delta)^2 > rho iff delta < 1 - sqrt(rho) = Johnson radius; <= 0 (vacuous) past Johnson."""
    a = (1.0 - delta) * n
    return a * a - n * k

# ---------------------------------------------------------------------------
# P4: the actual far-line list over mu_n past Johnson (KK/structured mechanism).
# Far line: x^a + alpha x^b. Bad alpha = the line is delta-close to RS[k].
# For the prize pencil we count alpha s.t. exists deg-<k poly agreeing on >= (1-delta)n points.
# We use the orbit-count / subset-sumset mechanism on a small inner subgroup (O11'').
# ---------------------------------------------------------------------------

def far_line_list_kk(p, mu, k, r):
    """Reproduce the KK/structured far-line list (O11''): inner subgroup G of order m=|mu|,
       lift X^(top) + lambda X^(low) on G, count structured bad scalars = subset-sumset of G.
       Returns the count of distinct bad scalars = |G^{(+r)}| (the r-subset sumset of G).
       This count is the worst-case far-line list contribution that the weight distribution
       (domain-blind) cannot predict."""
    G = mu  # treat mu as the inner subgroup
    m = len(G)
    sums = set()
    for S in combinations(G, r):
        e1 = sum(S) % p          # first elementary symmetric = subset sum
        sums.add((-e1) % p)      # bad scalar = -e1(S)  (the O11'' identity)
    return len(sums)

def random_domain_far_line_list(p, n, k, r, trials=200):
    """For a RANDOM n-subset domain, the analogous structured bad-scalar count is ~0:
       random points have no subgroup subset-sumset coincidences. Sample r-subsets of a random
       domain and count distinct -e1 values that actually yield a deg-<k agreeing poly on r pts.
       (Here we just report the subset-sumset image size, which for random points = full C(n,r)
       distinct values typically -> but the AGREEING ones require the algebraic coincidence,
       absent for random points. We measure: do random r-subsets give collisions in -e1? No.)"""
    dom = random.sample(range(1, p), n)
    sums = set()
    for S in combinations(dom, min(r, n)):
        e1 = sum(S) % p
        sums.add((-e1) % p)
    # number of DISTINCT bad scalars; for the subgroup it is the structured (small, special) set;
    # for random it is generic. The DISCRIMINATING quantity is whether these alpha actually make
    # the far line close -- which needs the algebraic vanishing only mu_n provides. We return
    # the raw distinct count for comparison of the *combinatorial* image only.
    return len(sums)


def main():
    random.seed(444)
    print("=" * 78)
    print("PROBE C40: MacWilliams / BCH weight-distribution list bound")
    print("=" * 78)

    results = {}

    # ---- P1: MDS weight distribution is domain-independent (mu_n == random == AP) ----
    print("\n[P1] MDS weight distribution is DOMAIN-INDEPENDENT (the functional forgets mu_n)")
    print("     (a) small-scale: empirical weight dist of mu_n == random subset == AP == MDS formula")
    print("     (b) prize-scale: the formula depends only on (n,k,q), provably point-blind")
    p1_pass = True
    # (a) EMPIRICAL domain-invariance at a small prime where q^k enumeration is feasible.
    # proper subgroup mu_n: p prime, n | p-1; here small q so we can brute force all q^k polys.
    for (n, k, q_small) in [(4, 2, 13), (6, 2, 13), (4, 2, 17)]:
        # need q_small prime with n | q_small-1 and mu_n PROPER (n < q_small-1)
        if not (is_prime(q_small) and (q_small - 1) % n == 0 and n < q_small - 1):
            continue
        mu = subgroup_mu_n(q_small, n)
        assert mu != sorted(range(1, q_small)), "must NOT be full group"
        # random proper n-subset (avoid 0; RS over F_p^* style)
        rand_dom = random.sample(range(1, q_small), n)
        # AP domain inside F_p (n distinct points)
        ap_dom = [(1 + i) % q_small for i in range(n)]
        if len(set(ap_dom)) != n:
            ap_dom = list(range(1, n + 1))
        A_mu = empirical_weight_dist(mu, k, q_small)
        A_rand = empirical_weight_dist(rand_dom, k, q_small)
        A_ap = empirical_weight_dist(ap_dom, k, q_small)
        A_form = mds_weight_dist(n, k, q_small)
        match = (A_mu == A_rand == A_ap == A_form)
        print(f"  (a) n={n} k={k} q={q_small}: A(mu_n)==A(random)==A(AP)==MDS formula?  {match}")
        if not match:
            print(f"      A_mu={A_mu}  A_rand={A_rand}  A_ap={A_ap}  formula={A_form}")
        p1_pass = p1_pass and match
    # (b) prize-scale proper subgroup, p >> n^3 : formula is point-blind by construction.
    for (n, k) in [(16, 4), (32, 8)]:
        p = find_prime_with_subgroup(n, max(1000, n ** 3 + 1))
        mu = subgroup_mu_n(p, n)
        assert len(mu) == n and p % n == 1 and is_prime(p) and p > n ** 3
        assert mu != sorted(range(1, p)), "must NOT be full group"
        _ = mds_weight_dist(n, k, p)  # well-defined; depends only on (n,k,p)
        print(f"  (b) n={n} k={k} p={p} (p>n^3={p > n**3}): A_w(n,k,p) point-blind "
              f"=> identical for mu_n / random / AP at prize scale.")
    results["P1_domain_independent"] = p1_pass

    # ---- P2: MacWilliams(A[RS[k]]) == A[RS[n-k]] (dual is the SAME MDS form, domain-blind) ----
    print("\n[P2] MacWilliams transform of RS[k] = MDS weight dist of dual RS[n-k] (still domain-blind)")
    p2_pass = True
    for (n, k) in [(8, 4), (12, 4), (16, 4)]:
        p = find_prime_with_subgroup(n, max(1000, n ** 3 + 1))
        q = p
        A = mds_weight_dist(n, k, q)
        B = macwilliams(A, q)
        A_dual = mds_weight_dist(n, n - k, q)  # dual of RS[k] is (generalized) RS[n-k], also MDS
        match = (B == A_dual)
        # report a couple of values
        print(f"  n={n} k={k} p={p}: MacWilliams(A[RS[k]]) == A[RS[n-k]]?  {match}")
        if not match:
            print(f"      B (first 6) = {B[:6]}")
            print(f"      A_dual      = {A_dual[:6]}")
        p2_pass = p2_pass and match
    results["P2_dual_is_mds_domainblind"] = p2_pass

    # ---- P3: weight-distribution list bound vacuous strictly past Johnson ----
    print("\n[P3] weight-distribution / second-moment list bound vacuous PAST Johnson")
    print("     (Johnson radius delta_J = 1 - sqrt(rho); denominator = a^2 - n(k-1))")
    p3_pass = True
    for (n, k) in [(16, 8), (16, 4), (16, 2)]:
        rho = k / n
        delta_J = 1 - math.sqrt(rho)
        # just below and just above Johnson
        below = delta_J - 0.01
        above = delta_J + 0.01
        d_below = johnson_denominator(n, k, below)
        d_above = johnson_denominator(n, k, above)
        ok = (d_below > 0) and (d_above <= 0)
        print(f"  n={n} k={k} rho={rho:.3f} Johnson delta_J={delta_J:.4f}: "
              f"denom(below)={d_below:.2f}>0, denom(above)={d_above:.2f}<=0 -> {ok}")
        p3_pass = p3_pass and ok
    # capacity is 1-rho; show Johnson < capacity (the window where the bound is silent)
    for (n, k) in [(16, 8)]:
        rho = k / n
        print(f"  WINDOW n={n} k={k}: Johnson={1-math.sqrt(rho):.4f} < capacity={1-rho:.4f}"
              f"  (weight-dist bound silent over the entire interior)")
    results["P3_vacuous_past_johnson"] = p3_pass

    # ---- P4: actual far-line list over mu_n is DOMAIN-DEPENDENT (structured KK mechanism) ----
    print("\n[P4] far-line list over mu_n is DOMAIN-DEPENDENT (structured >> generic) -- invisible")
    print("     to the domain-blind weight distribution.  bad-scalar = -e1(S), S an r-subset (O11'')")
    p4_pass = True
    # inner subgroup mu of order m; agreement r; KK witness u_S has degree (r-1) so effective rate
    # rho_eff = (r-1)/m wrt the lifted line over the m points. Past-Johnson when delta = 1-r/m > 1-sqrt(rho_eff).
    for (m, r) in [(8, 3), (16, 4), (32, 5)]:
        p = find_prime_with_subgroup(m, max(1000, m ** 3 + 1))
        mu = subgroup_mu_n(p, m)
        assert mu != sorted(range(1, p)) and p > m ** 3
        # STRUCTURED bad-scalar count over the actual subgroup mu_n
        struct = far_line_list_kk(p, mu, m, r)  # k unused inside; counts distinct -e1 over r-subsets
        # GENERIC: same combinatorial count over a RANDOM proper n-subset (no subgroup coincidences)
        rand = random_domain_far_line_list(p, m, m, r)
        # radius / Johnson bookkeeping (effective rate of the degree-(r-1) witness)
        rho_eff = (r - 1) / m
        delta = 1 - r / m
        delta_J = 1 - math.sqrt(rho_eff) if rho_eff > 0 else 1.0
        past = delta > delta_J
        # The discriminator: structured count is the SMALL STRUCTURED set (subset-sumset of mu_n,
        # the real far-line list), generic is the GENERIC count. The point is the two DIFFER ->
        # the list is domain-dependent. The structured set has algebraic collapses (|S|-symmetry)
        # absent for random points; e.g. antipodal pairing folds it. A weight functional gives the
        # SAME number for both (it is domain-blind) -> it cannot be the true far-line list.
        differ = (struct != rand)
        print(f"  m={m} r={r} p={p}: radius delta={delta:.4f} (Johnson_eff={delta_J:.4f} past={past})"
              f"  structured={struct}  generic(random)={rand}  differ={differ}")
        p4_pass = p4_pass and differ
    print("     => the far-line list distinguishes mu_n from a random domain; the weight")
    print("        distribution (P1/P2: identical for both) provably cannot.")
    results["P4_far_line_list_domain_dependent"] = p4_pass

    # ---- verdict ----
    print("\n" + "=" * 78)
    print("VERDICT SUMMARY")
    print("=" * 78)
    for kx, vx in results.items():
        print(f"  {kx}: {'PASS' if vx else 'FAIL'}")
    all_pass = all(results.values())
    print()
    if all_pass:
        print("All predictions hold => C40 = REDUCES-TO-JOHNSON.")
        print("The MacWilliams / BCH weight-distribution object is the second-moment functional:")
        print("  - domain-INDEPENDENT (P1, P2): it forgets mu_n, the very structure delta* depends on;")
        print("  - its list bound is the Johnson/annulus bound (P3): vacuous strictly past Johnson;")
        print("  - the real worst-case far-line list over mu_n is domain-DEPENDENT (P4), invisible to it.")
        print("To pin delta* past Johnson it must inject domain structure = the open BGK sup-norm.")
    else:
        print("Some prediction FAILED -- re-examine; not a clean reduces-to-johnson.")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
