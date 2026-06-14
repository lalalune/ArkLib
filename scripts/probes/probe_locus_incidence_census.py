#!/usr/bin/env python3
"""
probe_locus_incidence_census.py — the union-over-loci/incidence structure versus the
weight filter, measured exactly (issue #232; DISPROOF_LOG O94/O95 follow-up).

Setup: D <= F_q^* a negation-closed (even-order) multiplicative subgroup, |D| = n even,
D^2 its squaring image (|D^2| = n/2); errors are polynomials; wt(f) = #{x in D : f(x) != 0}.
O94: wt(f) <= w forces both coefficient slices to vanish on a dead pair-locus Z <= D^2
with |Z| >= n/2 - w (both slices vanish at y = x^2 iff f(x) = f(-x) = 0; char != 2).
O95: the homogeneous per-locus space {f : deg f < k, slices dead on Z} has exactly
q^max(0, k-2|Z|) elements.  Open (O95 frontier): union-over-loci vs the weight filter.

CENSUS 1 (code weight enumerator, the deg<k case): N(w) = #{f : deg f < k, wt f = w}
for (q,n,k) in {(17,8,2..4),(17,16,2..4),(13,12,2..4),(13,6,2..3),(257,16,2)}.
HARD CHECK against the classical MDS weight distribution (d = n-k+1):
  A_0 = 1,  A_w = C(n,w) * sum_{j=0}^{w-d} (-1)^j C(w,j) (q^{w-d+1-j} - 1)  for w >= d.
If it matches everywhere, the LEVEL-1 weight filter has a CLOSED FORM (RS is MDS) and
the table reports the looseness of the slice union bound SU(w) = C(n/2,z0) q^max(0,k-2z0)
(z0 = max(n/2-w, 0)) and the classical zero-locus union bound
CU(w) = C(n,n-w) q^max(0,k-(n-w)) against exact N<=(w).
Also HARD-CHECKS the homogeneous per-locus law for EVERY locus of size z <= floor(k/2)+1:
  #{f deg<k : f = 0 on both roots of every y in Z} = q^max(0, k-2|Z|).

CENSUS 2 (coset/LIST version — the actually-open object): received words u NOT in the
code (structured: x^k, x^{n-1}, all-nonzero noise, random high-coefficient part with
zero low part; plus 50 random), for (q,n,k) in {(17,16,2..4),(13,12,2..4)}.
For p in RS_k(D), the error f = interp(u) - p has its top n-k coefficients fixed by u;
its dead pair-locus is P_p(u) = {y in D^2 : p = u at both square roots of y}, and the
AFFINE per-locus space is A_Z(u) = {p : Z <= P_p(u)} = {p : p = u on the 2|Z| roots}.
HARD CHECKS (the conjectured affine laws):
  (i)   2|Z| <= k  ==>  |A_Z(u)| = q^{k-2|Z|} for EVERY Z and EVERY u (never empty);
  (ii)  2|Z| >  k  ==>  |A_Z(u)| in {0,1} (two deg<k polys agreeing on >k points match);
  (iii) mass identity: sum_{ALL p} C(|P_p(u)|, z) = C(n/2,z) q^{k-2z} for 2z <= k;
  (iv)  O94 on the coset: |P_p(u)| >= n/2 - wt(u-p) for every codeword p;
  (v)   ell(u,w) <= SU(w) and ell(u,w) <= interpolation bound C(n,k)/C(n-w,k);
  (vi)  coefficient cross-check on samples: interp(u-p) has top n-k coefficients
        independent of p, and the slice-vanishing pattern (even AND odd slice zero at y)
        equals the value-level pair pattern P_p(u).
MEASURES: ell(u,w) across unique-decoding -> Johnson -> capacity; incidence multiplicity
C(|P_p|, z0) of actual list elements; per-locus occupancy by list elements (served loci,
max occupancy); the weight-filter mass fraction I(w) / (C(n/2,z0) q^{k-2z0}); emptiness
fractions in the 0/1 regime 2z > k; the |P| histogram of list elements.

Exact arithmetic over GF(q) (q prime). Deterministic. Exit 0 iff all hard checks pass.
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


def make_domain(q, n):
    """Order-n multiplicative subgroup of GF(q)*, with pair (x,-x) bookkeeping."""
    g0 = pow(find_generator(q), (q - 1) // n, q)
    D, x = [], 1
    for _ in range(n):
        D.append(x)
        x = x * g0 % q
    assert len(set(D)) == n, f"subgroup order mismatch q={q} n={n}"
    Dset = set(D)
    if any((q - x) % q not in Dset for x in D):
        fail(f"domain q={q} n={n} NOT negation-closed")
    pos = {x: i for i, x in enumerate(D)}
    partner = [pos[(q - x) % q] for x in D]
    pair_id, pid = [-1] * n, 0
    for i in range(n):
        if pair_id[i] == -1:
            pair_id[i] = pair_id[partner[i]] = pid
            pid += 1
    assert pid == n // 2
    return D, partner, pair_id


def codewords(q, D, k):
    """All evaluation vectors of deg<k polynomials on D (the RS_k(D) code)."""
    words = [(0,) * len(D)]
    for j in range(k):
        bj = [pow(x, j, q) for x in D]
        words = [tuple((wi + c * bi) % q for wi, bi in zip(w, bj))
                 for w in words for c in range(q)]
    return words


def mds_A(q, n, k, w):
    d = n - k + 1
    if w == 0:
        return 1
    if w < d:
        return 0
    return C(n, w) * sum((-1) ** j * C(w, j) * (q ** (w - d + 1 - j) - 1)
                         for j in range(w - d + 1))


def polymul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] = (out[i + j] + ai * bj) % q
    return out


def interp_coeffs(xs, ys, q):
    """Coefficients (deg < len(xs)) of the Lagrange interpolant, exact mod q."""
    n = len(xs)
    full = [1]
    for x in xs:
        full = polymul(full, [(-x) % q, 1], q)
    coeffs = [0] * n
    for xj, yj in zip(xs, ys):
        if yj == 0:
            continue
        quot, carry = [0] * n, 0
        for i in range(n, 0, -1):
            carry = (full[i] + carry * xj) % q
            quot[i - 1] = carry
        denom = 0
        for c in reversed(quot):
            denom = (denom * xj + c) % q
        scale = yj * pow(denom, q - 2, q) % q
        for i in range(n):
            coeffs[i] = (coeffs[i] + scale * quot[i]) % q
    return coeffs


def eval_poly(coeffs, x, q):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def dead_pairs(p, u, n, partner, pair_id):
    """Sorted tuple of pair ids where p agrees with u at BOTH roots."""
    ag = [i for i in range(n) if p[i] == u[i]]
    wp = n - len(ag)
    if len(ag) < 2:
        return wp, ()
    ags = set(ag)
    return wp, tuple(sorted({pair_id[i] for i in ag if partner[i] in ags}))


# ====================================================================== CENSUS 1
print("=" * 78)
print("CENSUS 1: deg<k weight enumerator vs the classical MDS closed form")
print("=" * 78)

C1_SETUPS = [(17, 8, 2), (17, 8, 3), (17, 8, 4),
             (17, 16, 2), (17, 16, 3), (17, 16, 4),
             (13, 12, 2), (13, 12, 3), (13, 12, 4),
             (13, 6, 2), (13, 6, 3),
             (257, 16, 2)]
mds_all_match = True

for (q, n, k) in C1_SETUPS:
    D, partner, pair_id = make_domain(q, n)
    words = codewords(q, D, k)
    half = n // 2
    hist = [0] * (n + 1)
    for p in words:
        hist[sum(1 for v in p if v)] += 1
    mismatch = [w for w in range(n + 1) if hist[w] != mds_A(q, n, k, w)]
    if mismatch:
        mds_all_match = False
        fail(f"C1 MDS mismatch q={q} n={n} k={k} at w={mismatch}: "
             f"exact={[hist[w] for w in mismatch]} "
             f"mds={[mds_A(q, n, k, w) for w in mismatch]}")
    # homogeneous per-locus law, EVERY locus, z <= floor(k/2)+1
    zmax = min(k // 2 + 1, half)
    Ac = {z: {} for z in range(1, zmax + 1)}
    zero_u = (0,) * n
    for p in words:
        _, P = dead_pairs(p, zero_u, n, partner, pair_id)
        for z in range(1, min(len(P), zmax) + 1):
            for T in itertools.combinations(P, z):
                Ac[z][T] = Ac[z].get(T, 0) + 1
    locus_ok = True
    for z in range(1, zmax + 1):
        want = q ** max(0, k - 2 * z)
        vals = Ac[z]
        if len(vals) != C(half, z) or any(v != want for v in vals.values()):
            locus_ok = False
            fail(f"C1 homogeneous per-locus law q={q} n={n} k={k} z={z}: "
                 f"#loci={len(vals)}/{C(half, z)} "
                 f"values={sorted(set(vals.values()))[:6]} want={want}")
    d = n - k + 1
    print(f"\n-- q={q:3d} n={n:2d} k={k} d={d:2d}   MDS closed form: "
          f"{'MATCH (all w)' if not mismatch else 'MISMATCH'};  "
          f"homogeneous per-locus law (all loci, z<={zmax}): "
          f"{'OK' if locus_ok else 'BROKEN'}")
    print("    w z0          N(w)        N<=(w)        SU(w)    SU/N<=        "
          "CU(w)    CU/N<=")
    Nle = 0
    for w in range(n + 1):
        Nle += hist[w]
        z0 = max(half - w, 0)
        SU = C(half, z0) * q ** max(0, k - 2 * z0)
        CU = C(n, n - w) * q ** max(0, k - (n - w))
        print(f"   {w:2d} {z0:2d} {hist[w]:13d} {Nle:13d} {SU:12d} "
              f"{SU / Nle:9.3g} {CU:12d} {CU / Nle:9.3g}")

# ====================================================================== CENSUS 2
print()
print("=" * 78)
print("CENSUS 2: coset/list version — affine per-locus law, incidence, weight filter")
print("=" * 78)

NRAND = 50
C2_SETUPS = [(17, 16, 2), (17, 16, 3), (17, 16, 4),
             (13, 12, 2), (13, 12, 3), (13, 12, 4)]
STRUCT = ["xk", "xn1", "noise", "hifix"]

for (q, n, k) in C2_SETUPS:
    D, partner, pair_id = make_domain(q, n)
    words = codewords(q, D, k)
    wordset = set(words)
    half = n // 2
    zmax = min(k // 2 + 1, half)
    wUD = (n - k) // 2
    wJ = n - math.sqrt(n * k)
    wcap = n - k
    band = list(range(max(1, wUD - 1), wcap + 1))

    # received words u, never in the code
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
            fail(f"structured u {name} lies in the code (q={q} n={n} k={k})")

    # coefficient cross-check (vi) on the first structured u and 60 sampled p
    uref = us[0][1]
    f0 = interp_coeffs(D, [(uref[i]) % q for i in range(n)], q)
    sq_of_pair = {}
    for i in range(n):
        sq_of_pair[pair_id[i]] = pow(D[i], 2, q)
    for p in random.sample(words, min(60, len(words))):
        fc = interp_coeffs(D, [(uref[i] - p[i]) % q for i in range(n)], q)
        if fc[k:] != f0[k:]:
            fail(f"top-coefficient invariance broken q={q} n={n} k={k}")
        even = fc[0::2]
        odd = fc[1::2]
        _, P = dead_pairs(p, uref, n, partner, pair_id)
        for j, y in sq_of_pair.items():
            slice_dead = (eval_poly(even, y, q) == 0 and eval_poly(odd, y, q) == 0)
            if slice_dead != (j in P):
                fail(f"slice/value locus mismatch q={q} n={n} k={k} pair={j}")

    print(f"\n== q={q} n={n} k={k}: UD={wUD}  Johnson={wJ:.2f}  capacity={wcap}; "
          f"pair-locus active (z0>=1) iff w<={half - 1}; zmax={zmax}; "
          f"#u = 4 structured + {NRAND} random")

    per_w = {w: {"ells": {}, "inc": {}} for w in band}
    empt = {z: [] for z in range(1, zmax + 1) if 2 * z > k}
    phist_top = {}
    wtop = half - 1  # largest w with locus structure

    for name, u in us:
        whist = [0] * (n + 1)
        Ac = {z: {} for z in range(1, zmax + 1)}
        listel = []
        o94bad = 0
        for p in words:
            wp, P = dead_pairs(p, u, n, partner, pair_id)
            whist[wp] += 1
            if len(P) < half - wp:
                o94bad += 1
            for z in range(1, min(len(P), zmax) + 1):
                for T in itertools.combinations(P, z):
                    Ac[z][T] = Ac[z].get(T, 0) + 1
            if wp <= wcap:
                listel.append((wp, P))
        if o94bad:
            fail(f"O94 coset bound violated q={q} n={n} k={k} u={name}: "
                 f"{o94bad} codewords")
        for z in range(1, zmax + 1):
            vals = Ac[z]
            tot = C(half, z)
            if 2 * z <= k:
                want = q ** (k - 2 * z)
                if len(vals) != tot or any(v != want for v in vals.values()):
                    fail(f"affine per-locus law q={q} n={n} k={k} u={name} z={z}: "
                         f"#nonempty={len(vals)}/{tot} "
                         f"vals={sorted(set(vals.values()))[:6]} want={want}")
                if sum(vals.values()) != tot * want:
                    fail(f"mass identity q={q} n={n} k={k} u={name} z={z}")
            else:
                if vals and max(vals.values()) > 1:
                    fail(f"0/1 law broken q={q} n={n} k={k} u={name} z={z}: "
                         f"max={max(vals.values())}")
                empt[z].append(len(vals) / tot)

        cum, ellw = 0, {}
        for w in range(n + 1):
            cum += whist[w]
            ellw[w] = cum
        for w in band:
            z0 = half - w
            ell = ellw[w]
            per_w[w]["ells"].setdefault(name, []).append(ell)
            UBi = C(n, k) // C(n - w, k)
            if ell > UBi:
                fail(f"interp bound violated q={q} n={n} k={k} u={name} w={w}: "
                     f"ell={ell} > {UBi}")
            if 1 <= z0 <= zmax:
                els = [(wp, P) for (wp, P) in listel if wp <= w]
                if any(len(P) < z0 for _, P in els):
                    fail(f"list element below O94 locus floor q={q} n={n} k={k} "
                         f"u={name} w={w}")
                I = sum(C(len(P), z0) for _, P in els)
                occ = {}
                for _, P in els:
                    for T in itertools.combinations(P, z0):
                        occ[T] = occ.get(T, 0) + 1
                UBs = C(half, z0) * q ** max(0, k - 2 * z0)
                if ell > UBs:
                    fail(f"slice union bound violated q={q} n={n} k={k} u={name} "
                         f"w={w}: ell={ell} > {UBs}")
                nonemp = len(Ac[z0])
                per_w[w]["inc"].setdefault(name, []).append(
                    (I, len(occ), max(occ.values()) if occ else 0, nonemp,
                     max((len(P) for _, P in els), default=0)))
                if w == wtop:
                    for _, P in els:
                        key = len(P)
                        phist_top[key] = phist_top.get(key, 0) + 1

    # ---- report
    print("    w z0 |  ell: xk  xn1 nois hifx | randmax randmean |"
          "      UBslice UBinterp")
    for w in band:
        z0 = half - w
        e = per_w[w]["ells"]
        rands = e.get("rand", [0])
        UBs = (C(half, z0) * q ** max(0, k - 2 * z0)) if z0 >= 1 else q ** k
        UBi = C(n, k) // C(n - w, k)
        print(f"   {w:2d} {z0:2d} |      {e['xk'][0]:4d} {e['xn1'][0]:4d} "
              f"{e['noise'][0]:4d} {e['hifix'][0]:4d} | {max(rands):7d} "
              f"{sum(rands) / len(rands):8.2f} | {UBs:12d} {UBi:8d}")
    allmax = {w: max(x for v in per_w[w]["ells"].values() for x in v)
              for w in band}
    cross_n = min((w for w in band if allmax[w] > n), default=None)
    cross_n2 = min((w for w in band if allmax[w] > n * n), default=None)
    print(f"   max_u ell crosses n at w={cross_n}, n^2 at w={cross_n2} "
          f"(UD={wUD}, Johnson={wJ:.2f}, n/2={half})")
    for w in band:
        z0 = half - w
        if not (1 <= z0 <= zmax) or not per_w[w]["inc"]:
            continue
        inc = per_w[w]["inc"]
        flat = [t for v in inc.values() for t in v]
        Imax = max(t[0] for t in flat)
        servedmax = max(t[1] for t in flat)
        occmax = max(t[2] for t in flat)
        Pmax = max(t[4] for t in flat)
        tot = C(half, z0)
        if 2 * z0 <= k:
            denom = tot * q ** (k - 2 * z0)
            print(f"   incidence w={w} z0={z0}: I_max={Imax} "
                  f"(weight-filter mass fraction I/sumA = {Imax / denom:.2e}); "
                  f"loci served max {servedmax}/{tot}; max per-locus list occupancy "
                  f"{occmax}; max |P| of a list element {Pmax}")
        else:
            nonemp_max = max(t[3] for t in flat)
            print(f"   incidence w={w} z0={z0} (0/1 regime): I_max={Imax}; "
                  f"loci served max {servedmax}/{tot}; nonempty max {nonemp_max}/{tot}; "
                  f"max occupancy {occmax}; max |P| {Pmax}")
    for z in sorted(empt):
        es = empt[z]
        pred = 1 - math.exp(-q ** (k - 2 * z))
        print(f"   0/1 regime z={z} (2z>k): nonempty fraction over u "
              f"min/mean/max = {min(es):.4f}/{sum(es) / len(es):.4f}/{max(es):.4f} "
              f"(Poisson prediction 1-exp(-q^(k-2z)) = {pred:.4f})")
    if phist_top:
        print(f"   |P| histogram of list elements at w={wtop} (z0=1), all u: "
              f"{dict(sorted(phist_top.items()))} (O94 floor |P|>=1)")

print()
print(f"MDS closed-form verdict: "
      f"{'EXACT MATCH at every (q,n,k,w) tested' if mds_all_match else 'MISMATCH'}")
print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
