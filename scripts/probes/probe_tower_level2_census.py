#!/usr/bin/env python3
"""
probe_tower_level2_census.py — the TOWER ITERATION census: level-2 fold constraints
down the 2-adic chain, measured exactly (issue #232; DISPROOF_LOG O109 follow-up).

Setup: D <= F_q^* negation-closed subgroup, |D| = n with 4 | n, so D^2 (order n/2) is
itself negation-closed and D^4 = (D^2)^2 (order n/4) exists.  f deg < k splits into
slices fe (even coeffs, deg < ceil(k/2)) and fo (odd, deg < floor(k/2)) with
f(x) = fe(x^2) + x*fo(x^2).  Level-1 dead locus Z1(f) = {y in D^2 : fe(y)=fo(y)=0}
= {x^2 : f(x)=f(-x)=0} (O94); per-locus space exact q^(k-2|Z1|) (O96).  LEVEL 2: each
slice s in {fe,fo} on D^2 has its own slices (the four sub-slices ee,eo,oe,oo of f,
deg < ~k/4) and its own dead locus Z2(s) = {t in D^4 : s vanishes at both square roots
of t} in D^4.  This probe builds the first joint (Z1, Z2e, Z2o) census.

CENSUS 1 (homogeneous joint law): for (q,n,k) in {(17,16,4) exhaustive,
(17,16,8) sampled + exact min-weight stratum w=9, (257,16,4) sampled + stratum w=13,
(257,16,8) sampled + stratum w=9}: tabulate N(w; z1, z2e, z2o), HARD-CHECK per f:
O94 (z1 >= n/2-w), the FORCING inclusion pairs(Z1) subset Z2e & Z2o, the live-image
bound wt_{D^2}(slice) <= livepairs(f) = n/2 - z1, and O94-at-level-2
(z2 >= n/4 - wt_{D^2}(slice)).  N(w) is cross-checked against the MDS enumerator.

THE LEVEL-2 COUNTING LAW (the KEY QUESTION — answered YES, it is an exact q-power):
for every joint profile (Z1, Z2e, Z2o), with S_e = Z1 ∪ √Z2e, S_o = Z1 ∪ √Z2o
(√ = preimage of the squaring map D^2 -> D^4, |√Z| = 2|Z|):
    #{f : deg f < k, fe,fo vanish on Z1, Z2(fe) ⊇ Z2e, Z2(fo) ⊇ Z2o}
      = q^( max(0, ceil(k/2) - |S_e|) + max(0, floor(k/2) - |S_o|) ).
Verified EXHAUSTIVELY over all 2^16 profiles at (17,16,4) via a superset-zeta
transform, and at slice-budget 4 (k=8) by exact Vandermonde rank over GF(q) for every
S ⊆ D^2 (the law factorizes through the slice bijection: even constraints touch only
even coefficients).  Equivalently: LEVEL 2 REDUCES TO LEVEL 1 — the joint space is the
product of two level-1 vanishing spaces at the MERGED point sets; the naive product
dimension k - 2z1 - 2z2e - 2z2o is correct iff √Z2 ∩ Z1 = ∅; each overlap point
refunds exactly one dimension.

CENSUS 2 (THE DECIDING QUESTION): does the level-2 union bound
    LU2(w) = Σ_{|Z1|=z1°,|Z2e|=|Z2o|=z2°} q^((b_e-|S_e|)_+ + (b_o-|S_o|)_+),
z1° = (n/2-w)_+, z2° = (n/4-w)_+, beat the level-1 bound LU1(w) = C(n/2,z1°)q^(k-2z1°)
or the classical interpolation/zero-locus bound CU(w) = C(n,n-w)q^((k-(n-w))_+)
anywhere in the Johnson->capacity band?  Tabulated for k in {4,8} and the high-rate
setups (17,8,6),(17,16,10),(17,16,12),(17,16,14) where the two forced-activity windows
could first intersect.

CENSUS 3 (coset/list version): (17,16,4), (13,12,4), (17,8,4), 34 received words each
(4 structured + 30 random, never in the code): exact per-coset list sizes l(u,w),
the joint affine per-profile law (HARD CHECK, superset-zeta over all profiles:
#{p in RS_k : error slices vanish on S_e,S_o} = q^((b_e-|S_e|)+(b_o-|S_o|)) when under
budget, in {0, q-power} when over), O94-on-cosets, forcing inclusion, and the EXCESS
diagnostic: how often a coset element's level-2 locus strictly exceeds the part forced
by its level-1 locus.

================================ FINDINGS (this run) ================================
1. THE LEVEL-2 COUNTING LAW HOLDS EXACTLY — and it is a REDUCTION, not a new
   primitive.  All 65,536 joint profiles at (17,16,4) match
   q^((b_e-|S_e|)_+ + (b_o-|S_o|)_+) exactly (zeta-checked against the exhaustive
   census, MDS-cross-checked); all 256 Vandermonde ranks at slice budgets 2 and 4 are
   min(|S|,b) for q in {17,257}.  The per-(Z1,Z2-profile) space size IS again an
   exact q-power — but the exponent is k minus the sizes of the MERGED zero sets, so
   the level-2 analogue of card_polysDegLT_slices_vanishing is just
   card_polysDegLT_vanishing applied to S_e, S_o: dimensions subtract
   multiplicatively ONLY on disjoint profiles (√Z2 ∩ Z1 = ∅, e.g. the naive product
   k-2z1-2z2e-2z2o); every overlap point refunds exactly one dimension.  Affine/coset
   twin verified on 18 received words x all profiles (under-budget exact equality,
   over-budget in {0, q-power}).
2. THE FORCED LEVEL-2 LOCUS IS A SUBSET OF THE LEVEL-1 CONSTRAINT — zero new
   dimensions.  Hard-checked on every f/coset element examined (83,521 exhaustive +
   300k samples + full min-weight strata + 6.65M coset elements): pairs(Z1) ⊆
   Z2(fe) ∩ Z2(fo), and the O94-level-2 floor z2 >= n/4 - w is already met by
   pairs(Z1) alone (z1 >= n/2-w leaves <= w broken pairs).  Since √(pairs(Z1)) ⊆ Z1,
   the forced part of S_e is exactly Z1: the weight filter buys NO merged point
   beyond level 1.  The min-weight strata show the forcing live: (17,16,8) w=9 joint
   law is exact {(1,0,0):83968, (2,0,0):52224, (0,0,0):16384, (2,1,1):10240, ...} —
   the (2,1,1) class is precisely Z1 = one antipodal pair forcing one level-2 point
   per slice.  Excess level-2 deadness (a slice dying at a LIVE antipodal pair — the
   only independent channel) occurs at the accidental ~2*(n/4)*q^-2 null rate
   (measured 2.68%/3.39%/1.36% of coset elements at q in {17,13}, 1.6e-5/3.3e-6 of
   random f at q=257) and is NOT forced by the weight filter, so no union bound can
   spend it.
3. THE DECIDING QUESTION: NO — the level-2 union bound NEVER beats level-1, let
   alone classical interpolation, anywhere (band or not).  LU2(w) >= LU1(w) at every
   w of every setup (equality iff z2° = 0, i.e. all w >= n/4; LU2/LU1 in {16, 36,
   16, ...} up to 1008x WORSE below n/4): the fully-overlapped profiles alone
   reproduce LU1 termwise and the C(n/4,z2°)^2 multiplicity is pure overcounting.
   In the Johnson->capacity band: min LU2/CU = 3.71 (at (17,16,8), w=5), rising to
   2.4e6 — classical interpolation dominates BOTH fold levels everywhere in the
   band, extending O109's level-1 verdict to level 2.  Activity-window arithmetic:
   level-2 forcing needs w < n/4, level-1 under-budget needs w >= (n-k)/2; the
   windows intersect only when k >= n/2 + 2 (rate > 1/2 + 1/n) — EMPTY for k in
   {4,8} at n=16; at k=10/12/14 (n=16) and k=6 (n=8) the joint windows are
   [3]/[2,3]/[1,2,3]/[1] and there LU2/LU1 = 16/2.71/2.61-2.88/4 — still >= 1.
   Diagnosis: the tower multiplies CHOICES (C(n/4,z2°)^2 loci), not CONSTRAINTS
   (forced √Z2 ⊆ Z1 cuts zero extra dimensions); and the forced-activity threshold
   n/4 sits strictly below Johnson n-sqrt(nk) whenever k < 9n/16, so in the entire
   band even level-1 forcing is vacuous (z1° = 0 for k=4) or interpolation-dominated
   (k=8: LU1/CU = 3.71..5.4e5).  Level-ℓ generalization is immediate: forcing needs
   w < n/2^ℓ — the tower dies geometrically below the band.
4. COSET LISTS: level-2 thins NOTHING in the band.  At (17,16,4)/(13,12,4)/(17,8,4),
   34 received words each: lists stay empty/trivial (max ell <= 1) through Johnson
   up to ~capacity-2, cross n only at capacity-2/capacity-1, reproducing O109's
   floor-triviality; LU1 = LU2 on cosets at every band w (z2° = 0), and both exceed
   the interpolation bound by 2x-3200x.  List elements' level-2 loci equal
   pairs(P1) plus accidental excess at the null rate (4.5%/6.5%/5.2% of band list
   elements, concentrated at w = capacity where lists are the full C(n,k)/C(n-w,k)
   interpolation count) — uncorrelated with list membership.
5. PROPOSED THEOREM (the formalizable level-2 law — Lean route: recompose_slices +
   card_polysDegLT_vanishing at merged sets, NO new counting primitive):
   D negation-closed, 0 ∉ D, char F ≠ 2, 4 | |D|.  For Z1 ⊆ D², Z2e, Z2o ⊆ D⁴, let
   S_e = Z1 ∪ √Z2e, S_o = Z1 ∪ √Z2o ⊆ D².  Then
     #{f : deg f < k, evenSlice/oddSlice vanish on Z1, both slices of evenSlice f
        vanish at both roots of every t ∈ Z2e, same for oddSlice f on Z2o}
     = q^( max(0,⌈k/2⌉−|S_e|) + max(0,⌊k/2⌋−|S_o|) ),
   and for weight ≤ w errors the forced profile has √Z2 ⊆ Z1 — hence the level-≥2
   tower union bound is termwise ≥ the level-1 bound.  NEGATIVE VERDICT for the tower
   iteration as a counting mechanism: Conjecture-D content at level ≥ 2 must come from
   incidence/inclusion-exclusion or non-forced (anticorrelation) structure, not from
   multiplying forced per-level budgets.
=====================================================================================

Exact arithmetic over GF(q) (q prime).  Deterministic.  Exit 0 iff all hard checks
pass.
"""
import itertools
import math
import random
import sys

random.seed(232)
C = math.comb
ok = True
failures = 0


def fail(msg):
    global ok, failures
    ok = False
    failures += 1
    if failures <= 30:
        print("FAIL:", msg)


def popcount(m):
    return bin(m).count("1")


def find_generator(q):
    fac, m, d = [], q - 1, 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fac):
            return g
    raise ValueError(f"no generator mod {q}")


def make_tower(q, n):
    """Two levels of the 2-adic tower: D (order n, 4|n), D^2 (order n/2,
    negation-closed), D^4 (order n/4), with all pair bookkeeping."""
    assert n % 4 == 0 and (q - 1) % n == 0
    g0 = pow(find_generator(q), (q - 1) // n, q)
    D, x = [], 1
    for _ in range(n):
        D.append(x)
        x = x * g0 % q
    assert len(set(D)) == n
    pos = {v: i for i, v in enumerate(D)}
    if any((q - v) % q not in pos for v in D):
        fail(f"D not negation-closed q={q} n={n}")
    h2, h4 = n // 2, n // 4
    # D^2 with chosen representative roots
    D2, idx2, root1 = [], {}, []
    for i, v in enumerate(D):
        y = v * v % q
        if y not in idx2:
            idx2[y] = len(D2)
            D2.append(y)
            root1.append((i, pos[(q - v) % q]))
    assert len(D2) == h2
    if any((q - y) % q not in idx2 for y in D2):
        fail(f"D^2 not negation-closed q={q} n={n}")
    neg2 = [idx2[(q - y) % q] for y in D2]
    # D^4 via the squaring map D^2 -> D^4 (fibers are antipodal pairs of D^2)
    D4, idx4, root2 = [], {}, []
    for j, y in enumerate(D2):
        t = y * y % q
        if t not in idx4:
            idx4[t] = len(D4)
            D4.append(t)
            root2.append((j, neg2[j]))
    assert len(D4) == h4
    inv2 = pow(2, q - 2, q)
    xr = [D[i1] for (i1, i2) in root1]
    inv2x = [pow(2 * x % q, q - 2, q) for x in xr]
    # preimage table: D^4-mask -> D^2-mask of √
    pre4 = [0] * (1 << h4)
    for m in range(1 << h4):
        s = 0
        for t in range(h4):
            if m >> t & 1:
                s |= (1 << root2[t][0]) | (1 << root2[t][1])
        pre4[m] = s
    # forced table: D^2-mask Z1 -> D^4-mask of pairs(Z1) (both roots in Z1)
    forced2 = [0] * (1 << h2)
    for m in range(1 << h2):
        s = 0
        for t in range(h4):
            j1, j2 = root2[t]
            if m >> j1 & 1 and m >> j2 & 1:
                s |= 1 << t
        forced2[m] = s
    return dict(q=q, n=n, h2=h2, h4=h4, D=D, D2=D2, D4=D4, root1=root1,
                root2=root2, neg2=neg2, xr=xr, inv2=inv2, inv2x=inv2x,
                pre4=pre4, forced2=forced2)


def budgets(k):
    return (k + 1) // 2, k // 2  # even-slice and odd-slice degree budgets


def eval_poly(coeffs, x, q):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def slice_vals_from_evals(tw, ev):
    """Value-level slices: fe(y) = (f(x)+f(-x))/2, fo(y) = (f(x)-f(-x))/(2x)."""
    q = tw["q"]
    ve, vo = [], []
    for j, (i1, i2) in enumerate(tw["root1"]):
        a, b = ev[i1], ev[i2]
        ve.append((a + b) * tw["inv2"] % q)
        vo.append((a - b) * tw["inv2x"][j] % q)
    return ve, vo


def loci_from_slices(tw, ve, vo, ev):
    m1 = 0
    for j, (i1, i2) in enumerate(tw["root1"]):
        if ev[i1] == 0 and ev[i2] == 0:
            m1 |= 1 << j
    m2e = m2o = 0
    for t, (j1, j2) in enumerate(tw["root2"]):
        if ve[j1] == 0 and ve[j2] == 0:
            m2e |= 1 << t
        if vo[j1] == 0 and vo[j2] == 0:
            m2o |= 1 << t
    return m1, m2e, m2o


def check_forced(tw, wp, m1, ve, vo, m2e, m2o, ctx):
    """The forced-structure hard checks; returns (exc_e, exc_o)."""
    h2, h4 = tw["h2"], tw["h4"]
    z1 = popcount(m1)
    if z1 < h2 - wp:
        fail(f"O94 violated {ctx}: z1={z1} < {h2 - wp}")
    fmask = tw["forced2"][m1]
    if fmask & ~m2e or fmask & ~m2o:
        fail(f"forcing inclusion pairs(Z1) ⊆ Z2 violated {ctx}")
    livep = h2 - z1
    wt_ve = sum(1 for v in ve if v)
    wt_vo = sum(1 for v in vo if v)
    if wt_ve > livep or wt_vo > livep:
        fail(f"live-image bound violated {ctx}: wt(slice)>{livep}")
    if popcount(m2e) < h4 - wt_ve or popcount(m2o) < h4 - wt_vo:
        fail(f"O94-level-2 violated {ctx}")
    return popcount(m2e) - popcount(fmask), popcount(m2o) - popcount(fmask)


def mds_A(q, n, k, w):
    d = n - k + 1
    if w == 0:
        return 1
    if w < d:
        return 0
    return C(n, w) * sum((-1) ** j * C(w, j) * (q ** (w - d + 1 - j) - 1)
                         for j in range(w - d + 1))


def gf_rank(rows, q):
    rows = [r[:] for r in rows]
    rank, ncol = 0, (len(rows[0]) if rows else 0)
    for col in range(ncol):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], q - 2, q)
        rows[rank] = [v * inv % q for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                c = rows[i][col]
                rows[i] = [(v - c * w0) % q for v, w0 in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def zeta_superset(arr, nbits):
    for b in range(nbits):
        bit = 1 << b
        for m in range(len(arr)):
            if not m & bit:
                arr[m] += arr[m | bit]


def profile_pred(tw, k, z1m, z2e, z2o):
    be, bo = budgets(k)
    q = tw["q"]
    se = popcount(z1m | tw["pre4"][z2e])
    so = popcount(z1m | tw["pre4"][z2o])
    return q ** (max(0, be - se) + max(0, bo - so)), se, so


# ============================================================== bound functions
def lu1(tw, k, w):
    q, h2 = tw["q"], tw["h2"]
    be, bo = budgets(k)
    z1f = max(h2 - w, 0)
    return C(h2, z1f) * q ** (max(0, be - z1f) + max(0, bo - z1f))


def lu2(tw, k, w):
    q, h2, h4 = tw["q"], tw["h2"], tw["h4"]
    be, bo = budgets(k)
    z1f, z2f = max(h2 - w, 0), max(h4 - w, 0)
    tot = 0
    for Z1 in itertools.combinations(range(h2), z1f):
        m1 = 0
        for j in Z1:
            m1 |= 1 << j
        se_sum = so_sum = 0
        for Z2 in itertools.combinations(range(h4), z2f):
            m2 = 0
            for t in Z2:
                m2 |= 1 << t
            s = popcount(m1 | tw["pre4"][m2])
            se_sum += q ** max(0, be - s)
            so_sum += q ** max(0, bo - s)
        tot += se_sum * so_sum
    return tot


def cu(q, n, k, w):
    return C(n, n - w) * q ** max(0, k - (n - w))


# ====================================================================== CENSUS 1
print("=" * 78)
print("CENSUS 1: the joint level-1/level-2 locus law on the code (homogeneous)")
print("=" * 78)

HOM_SETUPS = [(17, 16, 4, "exhaustive"),
              (17, 16, 8, "sample"),
              (257, 16, 4, "sample"),
              (257, 16, 8, "sample")]
NSAMP = 100000
towers = {}


def get_tower(q, n):
    if (q, n) not in towers:
        towers[(q, n)] = make_tower(q, n)
    return towers[(q, n)]


def combination_consistency(tw, k, trials=30):
    """f(x) = fe(x^2) + x fo(x^2): value-level slices match coefficient slices."""
    q, n = tw["q"], tw["n"]
    be, bo = budgets(k)
    for _ in range(trials):
        f = [random.randrange(q) for _ in range(k)]
        ev = [eval_poly(f, x, q) for x in tw["D"]]
        ve, vo = slice_vals_from_evals(tw, ev)
        fe, fo = f[0::2], f[1::2]
        for j, y in enumerate(tw["D2"]):
            if ve[j] != eval_poly(fe, y, q) or vo[j] != eval_poly(fo, y, q):
                fail(f"slice value/coefficient mismatch q={q} n={n} k={k}")
                return


def census_f(tw, k, ve, vo, hist, arr, excs, mult=1, ctx=""):
    """Tabulate one f given its slice value vectors; returns its weight."""
    q, h2 = tw["q"], tw["h2"]
    xr = tw["xr"]
    m1, wp = 0, 0
    for j in range(h2):
        a, xb = ve[j], xr[j] * vo[j] % q
        v1, v2 = (a + xb) % q, (a - xb) % q
        if v1:
            wp += 1
        if v2:
            wp += 1
        if v1 == 0 and v2 == 0:
            m1 |= 1 << j
    m2e = m2o = 0
    for t, (j1, j2) in enumerate(tw["root2"]):
        if ve[j1] == 0 and ve[j2] == 0:
            m2e |= 1 << t
        if vo[j1] == 0 and vo[j2] == 0:
            m2o |= 1 << t
    ee, eo = check_forced(tw, wp, m1, ve, vo, m2e, m2o, ctx)
    key = (wp, popcount(m1), popcount(m2e), popcount(m2o))
    hist[key] = hist.get(key, 0) + mult
    if arr is not None:
        arr[m1 | m2e << h2 | m2o << (h2 + tw["h4"])] += mult
    excs[wp] = excs.get(wp, 0) + (mult if (ee or eo) else 0)
    return wp


def print_joint(tag, hist, n):
    print(f"   {tag} joint law N(w; z1, z2e, z2o):")
    for w in range(n + 1):
        row = {(z1, z2e, z2o): c for (ww, z1, z2e, z2o), c in hist.items()
               if ww == w}
        if not row:
            continue
        tot = sum(row.values())
        items = sorted(row.items(), key=lambda kv: -kv[1])
        s = ", ".join(f"{k}:{v}" for k, v in items[:5])
        more = f", +{len(items) - 5} profiles" if len(items) > 5 else ""
        print(f"     w={w:2d} N={tot:>12d}  {{{s}{more}}}")


for (q, n, k, mode) in HOM_SETUPS:
    tw = get_tower(q, n)
    h2, h4 = tw["h2"], tw["h4"]
    be, bo = budgets(k)
    d = n - k + 1
    combination_consistency(tw, k)
    print(f"\n-- q={q} n={n} k={k} (d={d})  D^2 order {h2}, D^4 order {h4}, "
          f"slice budgets ({be},{bo})  [{mode.upper()}]")

    # Vandermonde rank law for every S ⊆ D^2 at both budgets (the level-1 engine
    # the level-2 law reduces to)
    for b in {be, bo}:
        bad = 0
        for m in range(1 << h2):
            S = [tw["D2"][j] for j in range(h2) if m >> j & 1]
            rows = [[pow(y, i, q) for i in range(b)] for y in S]
            if gf_rank(rows, q) != min(len(S), b):
                bad += 1
        if bad:
            fail(f"Vandermonde rank law broken q={q} n={n} budget={b}: {bad} sets")
        else:
            print(f"   rank law: all {1 << h2} S ⊆ D^2 have rank = min(|S|,{b}) — "
                  f"per-slice vanishing space exactly q^({b}-|S|)_+")

    hist, excs = {}, {}
    arr = [0] * (1 << n) if mode == "exhaustive" else None

    if mode == "exhaustive":
        FE = []
        for fe in itertools.product(range(q), repeat=be):
            FE.append([eval_poly(fe, y, q) for y in tw["D2"]])
        FO = []
        for fo in itertools.product(range(q), repeat=bo):
            FO.append([eval_poly(fo, y, q) for y in tw["D2"]])
        for ve in FE:
            for vo in FO:
                census_f(tw, k, ve, vo, hist, arr, excs, ctx=f"hom q={q} k={k}")
        # MDS cross-check (the level-1 truth)
        for w in range(n + 1):
            Nw = sum(c for (ww, *_), c in hist.items() if ww == w)
            if Nw != mds_A(q, n, k, w):
                fail(f"MDS mismatch q={q} n={n} k={k} w={w}: {Nw} != "
                     f"{mds_A(q, n, k, w)}")
        print(f"   MDS enumerator: EXACT MATCH at every w (N total {q ** k})")
        print_joint("exhaustive", hist, n)
        # THE KEY QUESTION: all 2^n joint profiles vs the level-2 law
        zarr = arr[:]
        zeta_superset(zarr, n)
        badp = 0
        for z1m in range(1 << h2):
            for z2e in range(1 << h4):
                for z2o in range(1 << h4):
                    pred, se, so = profile_pred(tw, k, z1m, z2e, z2o)
                    actual = zarr[z1m | z2e << h2 | z2o << (h2 + h4)]
                    if actual != pred:
                        badp += 1
                        if badp <= 5:
                            fail(f"LEVEL-2 LAW broken q={q} k={k} "
                                 f"profile=({z1m:x},{z2e:x},{z2o:x}) "
                                 f"|S|=({se},{so}): {actual} != {pred}")
        if not badp:
            print(f"   LEVEL-2 LAW: all {1 << n} joint profiles match "
                  f"q^((be-|Se|)_+ + (bo-|So|)_+) EXACTLY")
    else:
        # exact minimum-weight stratum: f = c*loc_S, |S| = k-1 (loci independent
        # of the scalar c — multiplicity q-1 per zero-pattern)
        nS = 0
        for S in itertools.combinations(range(n), k - 1):
            ev = []
            for x in tw["D"]:
                v = 1
                for s in S:
                    v = v * (x - tw["D"][s]) % q
                ev.append(v)
            ve, vo = slice_vals_from_evals(tw, ev)
            w = census_f(tw, k, ve, vo, hist, None, excs, mult=q - 1,
                         ctx=f"stratum q={q} k={k}")
            if w != d:
                fail(f"stratum weight wrong q={q} k={k}: {w} != {d}")
            nS += 1
        Nd = sum(c for (ww, *_), c in hist.items() if ww == d)
        if Nd != mds_A(q, n, k, d):
            fail(f"stratum count vs MDS q={q} n={n} k={k}: {Nd} != "
                 f"{mds_A(q, n, k, d)}")
        print(f"   min-weight stratum w={d}: {nS} zero-patterns x (q-1) = {Nd} "
              f"= MDS A_{d} — EXACT")
        print_joint(f"stratum w={d} (exact)", {key: c for key, c in hist.items()
                                               if key[0] == d}, n)
        shist = {}
        for _ in range(NSAMP):
            fe = [random.randrange(q) for _ in range(be)]
            fo = [random.randrange(q) for _ in range(bo)]
            ve = [eval_poly(fe, y, q) for y in tw["D2"]]
            vo = [eval_poly(fo, y, q) for y in tw["D2"]]
            census_f(tw, k, ve, vo, shist, None, excs, ctx=f"samp q={q} k={k}")
        print_joint(f"sample ({NSAMP} f)", shist, n)
    etot = sum(excs.values())
    print(f"   excess level-2 deadness (z2 beyond pairs(Z1)): "
          f"{etot} occurrences "
          f"({etot / max(1, sum(c for c in hist.values()) + (NSAMP if mode != 'exhaustive' else 0)):.2e} of f) "
          f"by w: { {w: c for w, c in sorted(excs.items()) if c} }")

# ====================================================== CENSUS 2: deciding question
print()
print("=" * 78)
print("CENSUS 2: THE DECIDING QUESTION — LU2 vs LU1 vs classical CU vs exact N<=")
print("=" * 78)

DEC_SETUPS = [(17, 16, 4), (17, 16, 8), (257, 16, 4), (257, 16, 8),
              (17, 8, 6), (17, 16, 10), (17, 16, 12), (17, 16, 14)]
lu2_never_better = True
band_verdicts = []

for (q, n, k) in DEC_SETUPS:
    tw = get_tower(q, n)
    h2, h4 = tw["h2"], tw["h4"]
    wUD, wJ, wcap = (n - k) // 2, n - math.sqrt(n * k), n - k
    # activity windows: level-1 under budget needs 2*z1f <= k i.e. w >= (n-k)/2;
    # level-2 forcing needs w < n/4
    joint = [w for w in range(n + 1)
             if max(h2 - w, 0) * 2 <= k and max(h4 - w, 0) > 0]
    print(f"\n-- q={q} n={n} k={k}: UD={wUD} Johnson={wJ:.2f} capacity={wcap}; "
          f"L1 forced active w<{h2}, L2 forced active w<{h4}; "
          f"jointly active+under-budget w in {joint or 'EMPTY'}")
    print("    w z1° z2° |          N<=          LU1          LU2      LU2/LU1 |"
          "           CU   LU1/CU")
    Nle = 0
    for w in range(n + 1):
        Nle += mds_A(q, n, k, w)
        z1f, z2f = max(h2 - w, 0), max(h4 - w, 0)
        L1, L2, CUw = lu1(tw, k, w), lu2(tw, k, w), cu(q, n, k, w)
        if L2 < L1:
            lu2_never_better = False
            print("      *** LU2 < LU1 ***")
        if L1 < Nle or L2 < Nle:
            fail(f"union bound below truth q={q} n={n} k={k} w={w}")
        band = " <- band" if wJ <= w <= wcap else ""
        print(f"   {w:2d} {z1f:3d} {z2f:3d} | {Nle:13d} {L1:12d} {L2:12d} "
              f"{L2 / L1:12.4g} | {CUw:12d} {L1 / CUw:8.3g}{band}")
        if wJ <= w <= wcap:
            band_verdicts.append((q, n, k, w, L2 / CUw))

print(f"\nLU2 >= LU1 at EVERY w of every setup: {lu2_never_better} "
      f"(the level-2 union bound never improves on level-1)")
worst = min(band_verdicts, key=lambda t: t[4])
print(f"min over the Johnson->capacity band of LU2/CU = {worst[4]:.3g} at "
      f"(q,n,k,w)={worst[:4]} — classical interpolation dominates everywhere "
      f"iff this is >= 1: {worst[4] >= 1}")

# ====================================================================== CENSUS 3
print()
print("=" * 78)
print("CENSUS 3: coset/list version — joint affine law, excess, list thinning")
print("=" * 78)

COSET_SETUPS = [(17, 16, 4), (13, 12, 4), (17, 8, 4)]
NRAND = 30
NZETA = 6  # full all-profile zeta check on the first NZETA received words


def codewords(q, D, k):
    words = [(0,) * len(D)]
    for j in range(k):
        bj = [pow(x, j, q) for x in D]
        words = [tuple((wi + c * bi) % q for wi, bi in zip(w, bj))
                 for w in words for c in range(q)]
    return words


for (q, n, k) in COSET_SETUPS:
    tw = get_tower(q, n)
    h2, h4 = tw["h2"], tw["h4"]
    be, bo = budgets(k)
    D = tw["D"]
    words = codewords(q, D, k)
    wordset = set(words)
    wUD, wJ, wcap = (n - k) // 2, n - math.sqrt(n * k), n - k
    band = list(range(max(1, wUD - 1), wcap + 1))

    us = [("xk", tuple(pow(x, k, q) for x in D)),
          ("xn1", tuple(pow(x, n - 1, q) for x in D))]
    while True:
        u = tuple(random.randrange(1, q) for _ in range(n))
        if u not in wordset:
            us.append(("noise", u))
            break
    while True:
        hi = [0] * k + [random.randrange(q) for _ in range(n - k)]
        if not any(hi[k:]):
            continue
        u = tuple(eval_poly(hi, x, q) for x in D)
        if u not in wordset:
            us.append(("hifix", u))
            break
    nr = 0
    while nr < NRAND:
        u = tuple(random.randrange(q) for _ in range(n))
        if u not in wordset:
            us.append(("rand", u))
            nr += 1
    for name, u in us[:4]:
        if u in wordset:
            fail(f"structured u {name} in code (q={q} n={n} k={k})")

    print(f"\n== q={q} n={n} k={k}: UD={wUD} Johnson={wJ:.2f} capacity={wcap}; "
          f"#u = 4 structured + {NRAND} random; all-profile zeta on first {NZETA} u")

    root1, root2 = tw["root1"], tw["root2"]
    i2 = tw["inv2"]
    i2x = tw["inv2x"]
    xs = tw["xr"]
    per_w = {w: {} for w in band}
    exc_all = exc_n = 0
    exc_band = 0
    band_el = 0
    zeta_done = 0
    for ui, (name, u) in enumerate(us):
        whist = [0] * (n + 1)
        arr = [0] * (1 << n)
        listel = []
        for p in words:
            ev = [(ua - pa) % q for ua, pa in zip(u, p)]
            wp = n - ev.count(0)
            whist[wp] += 1
            m1 = 0
            ve = []
            vo = []
            for j in range(h2):
                i1, ii2 = root1[j]
                a, b = ev[i1], ev[ii2]
                if a == 0 and b == 0:
                    m1 |= 1 << j
                ve.append((a + b) * i2 % q)
                vo.append((a - b) * i2x[j] % q)
            m2e = m2o = 0
            for t in range(h4):
                j1, j2 = root2[t]
                if ve[j1] == 0 and ve[j2] == 0:
                    m2e |= 1 << t
                if vo[j1] == 0 and vo[j2] == 0:
                    m2o |= 1 << t
            arr[m1 | m2e << h2 | m2o << (h2 + h4)] += 1
            ee, eo = check_forced(tw, wp, m1, ve, vo, m2e, m2o,
                                  f"coset q={q} k={k} u={name}")
            exc_n += 1
            if ee or eo:
                exc_all += 1
            if wp <= wcap:
                listel.append((wp, m1, m2e, m2o, ee + eo))
        for (wp, m1, m2e, m2o, e) in listel:
            if wp >= wJ:
                band_el += 1
                if e:
                    exc_band += 1
        cum = 0
        ellw = {}
        for w in range(n + 1):
            cum += whist[w]
            ellw[w] = cum
        for w in band:
            per_w[w].setdefault(name, []).append(ellw[w])
            UBi = C(n, k) // C(n - w, k)
            if ellw[w] > UBi:
                fail(f"interp bound violated q={q} n={n} k={k} u={name} w={w}")
        if ui < NZETA:
            zeta_superset(arr, n)
            for z1m in range(1 << h2):
                for z2e in range(1 << h4):
                    pe = tw["pre4"][z2e]
                    for z2o in range(1 << h4):
                        se = popcount(z1m | pe)
                        so = popcount(z1m | tw["pre4"][z2o])
                        pred = q ** (max(0, be - se) + max(0, bo - so))
                        actual = arr[z1m | z2e << h2 | z2o << (h2 + h4)]
                        if se <= be and so <= bo:
                            if actual != pred:
                                fail(f"affine LEVEL-2 LAW q={q} k={k} u={name} "
                                     f"profile ({z1m:x},{z2e:x},{z2o:x}): "
                                     f"{actual} != {pred}")
                        elif actual not in (0, pred):
                            fail(f"affine over-budget law q={q} k={k} u={name}: "
                                 f"{actual} not in {{0,{pred}}}")
            zeta_done += 1

    print(f"   affine joint per-profile law: all {1 << n} profiles x {zeta_done} u "
          f"— under-budget EXACT q-power, over-budget in {{0, q-power}}")
    print("    w z1° z2° |  ell: xk  xn1 nois hifx | randmax randmean |"
          "      LU1=LU2     UBinterp")
    for w in band:
        z1f, z2f = max(h2 - w, 0), max(h4 - w, 0)
        e = per_w[w]
        rands = e.get("rand", [0])
        L1 = lu1(tw, k, w)
        UBi = C(n, k) // C(n - w, k)
        print(f"   {w:2d} {z1f:3d} {z2f:3d} |      {e['xk'][0]:4d} {e['xn1'][0]:4d} "
              f"{e['noise'][0]:4d} {e['hifix'][0]:4d} | {max(rands):7d} "
              f"{sum(rands) / len(rands):8.2f} | {L1:12d} {UBi:8d}")
    allmax = {w: max(x for v in per_w[w].values() for x in v) for w in band}
    cross_n = min((w for w in band if allmax[w] > n), default=None)
    print(f"   max_u ell crosses n at w={cross_n} "
          f"(UD={wUD}, Johnson={wJ:.2f}, capacity={wcap})")
    print(f"   excess level-2 deadness: {exc_all}/{exc_n} coset elements "
          f"({exc_all / exc_n:.2%}); among band list elements (w>=Johnson): "
          f"{exc_band}/{band_el}")

print()
print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
