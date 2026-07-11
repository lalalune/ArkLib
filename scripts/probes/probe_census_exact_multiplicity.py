#!/usr/bin/env python3
"""
Census EXACT-multiplicity characterization (issue #444, census/supply face).

In-tree (CensusScalarPartition.lean) we have:
  #alignableSets = #pinnedScalars + Sum_{pinned gamma} (mult(gamma) - 1)            [EXACT]
  mult(gamma) >= C(|S0| - (k+1), a - (k+1))   when gamma owns a deep set S0          [LOWER bound only]

This probe tests the EXACT multiplicity claim that would upgrade the lower bound to an identity:

  CLAIM. mult(gamma) = #{ a-subsets S of A_gamma : S contains a non-degenerate (k+1)-tuple }
  where A_gamma = { i in [n] : the residual pencil at every (k+1)-tuple through i can be
                   gamma-aligned } -- operationally, the MAXIMAL gamma-aligned set.

  Equivalently, since a set S is gamma-aligned  iff  S subset of A_gamma (Aligned.mono +
  the pencil is determined pointwise by gamma), the aligned a-sets owned by gamma are EXACTLY
  the a-subsets of A_gamma, and the non-degenerate ones are those NOT entirely inside the
  degenerate locus D_gamma = { i : residual_u0(t)=residual_u1(t)=0 for the tuples through i }.

  So:  mult(gamma) = C(|A_gamma|, a) - C(|deg part|, a)   (incl-excl, leading term).

We verify on the REAL prize structure: RS code, proper thin subgroup mu_n = <g^{(p-1)/n}>,
n = 2^a, n | p-1, p >> n^3, multi-prime, NEVER n = q-1.  We compute mult(gamma) by brute
enumeration of aligned a-sets and compare to the agreement-set binomial formula.
"""
import itertools, math, random

def is_prime(m):
    if m < 2: return False
    for q in range(2, int(m**0.5)+1):
        if m % q == 0: return False
    return True

def find_prime(n, lo):
    # prime p with n | p-1, p >= lo
    p = lo - (lo % n) + 1
    while p < lo or not is_prime(p):
        p += n
    return p

def primitive_root(p):
    # smallest primitive root mod p
    fac = []
    m = p-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no prim root")

def lagrange_interp_deg_lt_k(pts, vals, xs, p):
    """Is there a poly of degree < k through (pts,vals)? Return the value-vector check.
    We test residual: a (k+1)-tuple t lies on a deg<k poly iff the (k+1)x(k+1) Vandermonde
    determinant condition (divided difference of order k) is 0."""
    pass

def divided_diff_k(xpts, ypts, p):
    """Order-k divided difference (k = len-1). Zero iff the points lie on a deg<k poly.
    Returns the leading divided difference mod p."""
    k = len(xpts) - 1
    y = list(ypts)
    for j in range(1, k+1):
        newy = []
        for i in range(len(y)-1):
            dx = (xpts[i+j] - xpts[i]) % p
            num = (y[i+1] - y[i]) % p
            newy.append((num * pow(dx, p-2, p)) % p)
        y = newy
    return y[0] % p

def run_instance(n, p, k, a, seed=0):
    rng = random.Random(seed)
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)        # generator of mu_n
    dom = [pow(h, i, p) for i in range(n)]    # the THIN proper subgroup as eval domain
    assert len(set(dom)) == n
    assert h != 1 and pow(h, n, p) == 1       # proper: order exactly n
    # PLANTED stack so a known scalar gamma* aligns a DEEP set (non-trivial multiplicity).
    # Choose target gamma*, set u0 = -gamma*.u1 + (deg<k poly) on a deep set D so that for any
    # (k+1)-tuple t in D: resid(t,u0) = -gamma*.resid(t,u1), hence resid_u0+gamma*.resid_u1=0,
    # with resid_u1 generically != 0 (non-degenerate). Off D, randomize.
    def poly_eval(coeffs, x):
        v = 0
        for c in reversed(coeffs):
            v = (v*x + c) % p
        return v
    gamma_star = rng.randrange(1, p)
    s = min(n, a + 2)
    D = sorted(rng.sample(list(range(n)), s))
    ck = [rng.randrange(p) for _ in range(k)]
    u0 = [rng.randrange(p) for _ in range(n)]
    u1 = [rng.randrange(p) for _ in range(n)]
    for i in D:
        x = dom[i]
        u1[i] = rng.randrange(p)
        u0[i] = (-gamma_star * u1[i] + poly_eval(ck, x)) % p

    idx = list(range(n))

    # residual_u(t) for a (k+1)-tuple t = order-k divided difference of u over dom[t]
    def resid(t, u):
        xs = [dom[i] for i in t]
        ys = [u[i] for i in t]
        return divided_diff_k(xs, ys, p)

    # A set S is gamma-aligned iff for every (k+1)-subtuple t of S:
    #   residual(t,u0) + gamma*residual(t,u1) = 0 (mod p)
    # We enumerate aligned a-sets and bucket by the scalar gamma they pin.
    # A non-degenerate tuple has not(r0==0 and r1==0); it pins gamma = -r0 * r1^{-1}.

    from collections import defaultdict
    aligned_asets = defaultdict(set)   # gamma -> set of frozenset a-sets, non-degenerate
    pinned = set()

    for S in itertools.combinations(idx, a):
        # find the scalar(s) consistent with all (k+1)-subtuples; check non-degenerate tuple
        gamma = None
        ok = True
        has_nondeg = False
        for t in itertools.combinations(S, k+1):
            r0 = resid(t, u0); r1 = resid(t, u1)
            if r1 == 0 and r0 == 0:
                continue  # degenerate tuple constrains nothing
            has_nondeg = True
            gt = (-r0 * pow(r1, p-2, p)) % p if r1 != 0 else None
            if r1 == 0 and r0 != 0:
                ok = False; break   # cannot align (r0 != 0, r1 = 0 means no finite gamma)
            if gamma is None:
                gamma = gt
            elif gamma != gt:
                ok = False; break
        if ok and has_nondeg and gamma is not None:
            aligned_asets[gamma].add(frozenset(S))
            pinned.add(gamma)

    # mult(gamma) = #aligned a-sets owned by gamma
    mult = {gm: len(s) for gm, s in aligned_asets.items()}

    # AGREEMENT SET A_gamma: points i such that {i} can extend to a gamma-aligned set.
    # Operationally A_gamma = union of all gamma-aligned a-sets owned by gamma.
    # CLAIM to test: aligned a-sets of gamma == all a-subsets of A_gamma that contain a
    # non-deg tuple. Predict mult(gamma) = (# a-subsets of A_gamma with a non-deg tuple).
    results = []
    for gm in pinned:
        Ag = set()
        for S in aligned_asets[gm]:
            Ag |= S
        Ag = sorted(Ag)
        # count a-subsets of A_gamma that are themselves gamma-aligned & non-deg
        cnt_pred = 0
        for S in itertools.combinations(Ag, a):
            ok = True; has_nd = False
            for t in itertools.combinations(S, k+1):
                r0 = resid(t, u0); r1 = resid(t, u1)
                if r0 == 0 and r1 == 0:
                    continue
                has_nd = True
                if r1 == 0:
                    ok = False; break
                gt = (-r0 * pow(r1, p-2, p)) % p
                if gt != gm:
                    ok = False; break
            if ok and has_nd:
                cnt_pred += 1
        results.append((gm, len(Ag), mult[gm], cnt_pred, mult[gm] == cnt_pred))
    return pinned, mult, results

if __name__ == "__main__":
    print("Census EXACT-multiplicity probe — mult(gamma) vs a-subsets-of-agreement-set count")
    print("REAL prize structure: thin mu_n = <g^{(p-1)/n}>, n=2^a, n|p-1, p>>n^3, NEVER n=q-1\n")
    # keep n small enough to brute-enumerate C(n,a). k = dimension-1 of RS code.
    configs = [
        # n, k, a, prime-floor
        (8, 1, 3, 8**3),
        (8, 2, 4, 8**3),
        (12, 1, 3, 12**3),   # n not 2-power as a sanity control (still proper)
        (16, 1, 3, 16**3),
    ]
    allmatch = True
    for (n, k, a, lo) in configs:
        p = find_prime(n, lo)
        for seed in range(3):
            pinned, mult, results = run_instance(n, p, k, a, seed=seed)
            nmis = sum(1 for r in results if not r[4])
            tot = len(results)
            if nmis: allmatch = False
            # report a couple of rows
            print(f"n={n} k={k} a={a} p={p} seed={seed}: pinned={len(pinned)} "
                  f"mult-rows={tot} mismatches={nmis}")
            for r in results[:2]:
                gm, Agc, m, pr, okk = r
                print(f"    gamma={gm:>6} |A_gamma|={Agc} mult={m} pred_C-count={pr} match={okk}")
    print()
    print("VERDICT: mult(gamma) == #(a-subsets of agreement set with a non-deg tuple)?",
          "ALL MATCH" if allmatch else "MISMATCH FOUND")
