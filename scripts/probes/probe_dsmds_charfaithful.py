"""
probe_dsmds_charfaithful.py  (issue #407 / #389 -- DO NOT COMMIT)

TARGET: Is mu_n's higher-order-MDS (MDS(3), MDS(4)) structure CHARACTERISTIC-FAITHFUL?

BGM (arXiv 2310.12888) Def 1.2: a code C with generator G is MDS(ell) iff for ALL subsets
A_1,...,A_ell of [n]:  dim(G_{A_1} cap ... cap G_{A_ell}) = dim(W_{A_1} cap ... cap W_{A_ell})
with W GENERIC. BGM footnote 333: the RHS (generic baseline) is CHARACTERISTIC-INDEPENDENT.
So MDS(ell)-ness reduces to: does mu_n's ACTUAL (LHS) intersection dim match the (char-indep)
generic value -- and is THAT a char-faithful question?

For the RS / Vandermonde frame v_i = (1, x_i, x_i^2, ..., x_i^{k-1}) the pair-span of a 2-set
{a,b} is the hyperplane orthogonal to the interpolation normal (x_a x_b, -(x_a+x_b), 1) (k=3
case, in-tree HigherOrderMDSOrderThreeChar.lean). Generic position of ell disjoint pairs at
order ell=k fails iff the ell x ell determinant of the (elementary-symmetric) normals vanishes
= a generalized-Vandermonde / Schur minor. MDS(ell) at the worst configuration = a CONJUNCTION
of such minor-nonvanishings over all subset-tuples = OVER-DETERMINED (>= 2 simultaneous
conditions for ell >= 3 distinct pairs because each (k+1)-incidence is itself >= 2 minors).

This probe TESTS, for the SPECIFIC subgroup mu_n (n = 2^a), whether the determinants that
DEFINE generic-position-failure (i.e. the MDS(ell) obstruction minors):
  (1) vanish in char 0 EXACTLY at the antipodal / coset-closure configs (the in-tree fact), and
  (2) for NON-antipodal configs, are NONZERO mod every large prime q >> n^2 (char-faithful) --
      i.e. mu_n's MDS(ell)-ness = char-0 MDS(ell)-ness for q >> T(n).

We contrast OVER-determined (the genuine MDS(ell) conjunction, ell>=3 pairs at order k) against
the UNDER-determined single-incidence object (one normal-determinant / subset-sum) which is the
known BGK wall. HONESTY: proper subgroups, big primes q >> n^2 (and beyond n^4); exact char-0
via complex det with tolerance; antipodal configs flagged; nothing committed.
"""
import sympy, math, cmath, itertools, random
import numpy as np
random.seed(11)
TAU = 2 * math.pi

# ---------- char-0 : complex roots of unity ----------
def zeta_c(n, e):  # e-th power of primitive n-th root, complex
    return cmath.exp(1j * TAU * (e % n) / n)

def char0_det(rows):
    return abs(np.linalg.det(np.array(rows, dtype=complex)))

# ---------- char-p : zeta = primitive n-th root mod q ----------
def detmodq(rows, q):
    m = len(rows); A = [[x % q for x in r] for r in rows]; det = 1
    for i in range(m):
        piv = next((r for r in range(i, m) if A[r][i] % q), None)
        if piv is None: return 0
        if piv != i: A[i], A[piv] = A[piv], A[i]; det = -det
        det = (det * A[i][i]) % q; inv = pow(A[i][i], q - 2, q)
        for r in range(i + 1, m):
            f = (A[r][i] * inv) % q
            if f: A[r] = [(A[r][c] - f * A[i][c]) % q for c in range(m)]
    return det % q

def primes_q1modn(n, count, start_m=1):
    """primes q = n*m + 1 (so mu_n exists in F_q), ascending; skip Fermat-ish high-2-adic."""
    out = []; m = start_m
    while len(out) < count:
        q = n * m + 1
        if sympy.isprime(q):
            # avoid pure 2-power high-v2 (Fermat) per honesty contract: require m have an odd factor
            if m % 2 == 1 or (m & (m - 1)) != 0:
                out.append(q)
        m += 1
    return out

def zeta_modq(n, q):
    g = sympy.primitive_root(q)
    return pow(g, (q - 1) // n, q)

# ============================================================================
# The MDS(ell)-obstruction minor for ell disjoint PAIRS at order k = ell.
# Pair {a,b} normal in dim k: coeff vector of prod_{j}(X - x_{a or b}) for the
# k-1 ... here we use the ORDER-ell generalized object: ell disjoint (ell-1)-subsets?
# We follow the in-tree order-3 law (pairs, k=3) and its order-4 generalization:
#   at order ell, take ell disjoint pairs; the obstruction = det of the ell x ell
#   matrix whose row i is the interpolation normal of pair i truncated/lifted to
#   the relevant symmetric coordinates. For order 3 (k=3): normal=(p_i,-s_i,1),
#   det = (sum,product) collinearity. For order 4 (k=4): pairs span planes in K^4;
#   generic intersection of 4 planes (codim 2 each) in K^4 is 0-dim (budget 8>4) so
#   we instead test the MDS(4) defining object: 4 disjoint pairs, intersection of the
#   4 plane-spans should be {0}; failure = a 4x4-block rank drop. We test the natural
#   generalized-Vandermonde minor det of the stacked normals (each pair contributes
#   its (k=4) normal coeff vector of (X-x_a)(X-x_b) = (x_a x_b, -(x_a+x_b), 1, 0) and
#   its X*that shift (0, x_a x_b, -(x_a+x_b), 1)) -> 4 covectors, 4x4 det.
# ============================================================================

def pair_normal_k3(xa, xb):
    return [xa * xb, -(xa + xb), 1.0]

def pair_normal_k3_q(za, zb, q):
    return [(za * zb) % q, (-(za + zb)) % q, 1 % q]

def order3_minor_c(n, pairs):
    rows = [pair_normal_k3(zeta_c(n, a), zeta_c(n, b)) for (a, b) in pairs]
    return char0_det(rows)

def order3_minor_q(n, pairs, q, zeta):
    za = lambda e: pow(zeta, e % n, q)
    rows = [pair_normal_k3_q(za(a), za(b), q) for (a, b) in pairs]
    return detmodq(rows, q)

# order 4: 3 disjoint pairs give 3 planes (codim 2) in K^4, budget 6 > 4 -> generic
# intersection {0}; failure = stacked 6 covectors (2 per pair) have rank < 4, i.e. ALL
# 4x4 minors of the 6x4 matrix vanish (OVER-determined: C(6,4)=15 simultaneous minors).
def pair_covectors_k4(za, zb):  # two shifts of (za*zb, -(za+zb), 1) in dim 4
    p = za * zb; s = za + zb
    return [[p, -s, 1, 0], [0, p, -s, 1]]

def pair_covectors_k4_q(za, zb, q):
    p = (za * zb) % q; s = (za + zb) % q
    return [[p % q, (-s) % q, 1 % q, 0], [0, p % q, (-s) % q, 1 % q]]

def order4_minors_c(n, pairs):  # returns max |minor| over all 4x4 minors of 6x4
    M = []
    for (a, b) in pairs:
        M += pair_covectors_k4(zeta_c(n, a), zeta_c(n, b))
    M = np.array(M, dtype=complex)
    return max(abs(np.linalg.det(M[list(idx), :])) for idx in itertools.combinations(range(6), 4))

def order4_allminors_zero_q(n, pairs, q, zeta):
    za = lambda e: pow(zeta, e % n, q)
    M = []
    for (a, b) in pairs:
        M += pair_covectors_k4_q(za(a), za(b), q)
    return all(detmodq([M[i] for i in idx], q) == 0 for idx in itertools.combinations(range(6), 4))

def is_antipodal_pair(n, a, b):
    return (a + b) % n == 0  # x_a + x_b = 0  <=>  x_b = -x_a  (n even)

def disjoint_pairs(n, count):
    """random disjoint pairs from Z/n, NO antipodal pairs (proper / generic-flavored)."""
    pts = list(range(n)); random.shuffle(pts)
    chosen = []
    used = set()
    for a in pts:
        if a in used: continue
        for b in pts:
            if b in used or b == a: continue
            if is_antipodal_pair(n, a, b): continue
            chosen.append((a, b)); used.add(a); used.add(b); break
        if len(chosen) == count: break
    return chosen if len(chosen) == count else None

def antipodal_pairs(n, count):
    chosen = []; used = set()
    for a in range(n):
        b = (-a) % n
        if a in used or b in used or b == a: continue
        chosen.append((a, b)); used.add(a); used.add(b)
        if len(chosen) == count: break
    return chosen if len(chosen) == count else None

print("="*78)
print("PROBE: mu_n higher-order-MDS char-faithfulness  (MDS(3) via order-3 minors)")
print("="*78)
print("Claim under test: for NON-antipodal disjoint-pair configs of mu_n, the MDS(3)")
print("obstruction minor (sum,product collinearity det) is NONZERO in char 0 AND mod")
print("every large prime q = n*m+1 >> n^2  (=> char-faithful). Antipodal configs vanish")
print("in char 0 already (the only failure).")
print()

for n in [8, 16, 32]:
    k = 3
    print(f"--- n={n}  (mu_n, order ell=k=3, three disjoint pairs) ---")
    # (a) antipodal config: should be char-0 ZERO (the in-tree only-failure)
    ap = antipodal_pairs(n, 3)
    if ap:
        c0 = order3_minor_c(n, ap)
        print(f"  antipodal pairs {ap}: |char0 det| = {c0:.3e}  -> {'VANISH (expected failure)' if c0<1e-7 else 'nonzero?!'}")
    # (b) non-antipodal generic configs: char-0 nonzero, then probe mod many large primes
    n_cfg = 40
    cfgs = []
    tries = 0
    while len(cfgs) < n_cfg and tries < n_cfg*40:
        tries += 1
        pr = disjoint_pairs(n, 3)
        if pr is None: continue
        c0 = order3_minor_c(n, pr)
        if c0 > 1e-7:  # char-0 generic-position (MDS(3) holds here in char 0)
            cfgs.append(pr)
    # also keep any char-0 collinear-but-non-antipodal (distinct-sum failure, like Dcol)
    distinct_sum_fail = []
    tries = 0
    while len(distinct_sum_fail) < 3 and tries < 4000:
        tries += 1
        pr = disjoint_pairs(n, 3)
        if pr is None: continue
        sums = {(a+b)%n for (a,b) in pr}
        if len(sums) == 3 and order3_minor_c(n, pr) < 1e-7:
            distinct_sum_fail.append(pr)
    qs = primes_q1modn(n, 60)
    big = [q for q in qs if q > n*n]
    veryig = [q for q in qs if q > n**4]
    bad_primes = {}  # config -> list of q where char-p det == 0 but char-0 nonzero
    for pr in cfgs:
        for q in qs:
            z = zeta_modq(n, q)
            if order3_minor_q(n, pr, q, z) == 0:
                bad_primes.setdefault(tuple(pr), []).append(q)
    n_faithful = sum(1 for pr in cfgs if tuple(pr) not in bad_primes)
    print(f"  non-antipodal char-0-generic configs tested: {len(cfgs)}")
    print(f"  primes probed: {len(qs)} (max q={max(qs)} ~ n^{math.log(max(qs))/math.log(n):.2f});  "
          f"{len(big)} with q>n^2, {len(veryig)} with q>n^4")
    if bad_primes:
        worst = max(max(v) for v in bad_primes.values())
        print(f"  CONFIGS WITH A BAD PRIME (spurious char-p vanish): {len(bad_primes)}/{len(cfgs)};  "
              f"worst bad prime = {worst} = n^{math.log(worst)/math.log(n):.2f}")
        print(f"    -> bad primes confined below: {'n^2' if worst<=n*n else 'ABOVE n^2'}; "
              f"none above n^4: {all(max(v)<=n**4 for v in bad_primes.values())}")
    else:
        print(f"  *** ZERO bad primes across all {len(cfgs)} configs x {len(qs)} primes "
              f"(up to n^{math.log(max(qs))/math.log(n):.2f}) -> CHAR-FAITHFUL ***")
    print(f"  faithful configs (char-p = char-0 for ALL probed q): {n_faithful}/{len(cfgs)}")
    if distinct_sum_fail:
        print(f"  (distinct-sum char-0 failures found {len(distinct_sum_fail)}, e.g. {distinct_sum_fail[0]} "
              f"-- these vanish in char 0 too, the (sum,product)-collinear non-antipodal failure mode)")
    print()

print("="*78)
print("PROBE: MDS(4) -- OVER-determined (3 disjoint pairs, 6 covectors in K^4, C(6,4)=15")
print("simultaneous 4x4 minors must ALL vanish for a failure).  Over-det => should be")
print("char-faithful with NO bad primes (the s-k>=2 / over-det rigidity regime).")
print("="*78)
for n in [8, 16, 32]:
    print(f"--- n={n}  (order 4 conjunction) ---")
    # char-0: 3 generic disjoint pairs -> NOT all minors vanish (MDS(4) holds generically)
    n_cfg = 30; cfgs = []; tries = 0
    while len(cfgs) < n_cfg and tries < n_cfg*40:
        tries += 1
        pr = disjoint_pairs(n, 3)
        if pr is None: continue
        if order4_minors_c(n, pr) > 1e-7:  # char-0 MDS(4) generic-position
            cfgs.append(pr)
    qs = primes_q1modn(n, 50)
    bad = 0
    for pr in cfgs:
        for q in qs:
            z = zeta_modq(n, q)
            if order4_allminors_zero_q(n, pr, q, z):  # spurious total rank-drop mod q
                bad += 1; break
    print(f"  char-0-generic configs: {len(cfgs)}; primes: {len(qs)} (max q={max(qs)} = "
          f"n^{math.log(max(qs))/math.log(n):.2f}); configs with a spurious char-p TOTAL "
          f"minor-vanish: {bad}")
    print(f"  -> {'CHAR-FAITHFUL (over-det rigidity: 0 bad)' if bad==0 else 'BAD PRIMES FOUND'}")
print()
print("CONTRAST (under-determined / BGK, from prior fleet probes): a SINGLE incidence object")
print("(one subset-sum / Schur h_{b-k} = 0) has bad primes GROWING n^3.25 -> 3.95 -> 5.99.")
print("The MDS(ell) conjunction is over-determined => bad primes stay below ~n^2 (or vanish).")
