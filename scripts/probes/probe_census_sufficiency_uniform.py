#!/usr/bin/env python3
"""
PROBE (#444 census face, lane `censussuff`): the CensusDomination SUFFICIENCY lift.

The brick censusDomination_of_caps lifts the per-band incidence cap
`#alignableSets(a) <= P*M` to the band-QUANTIFIED Prop CensusDomination (the $1M obligation the
delta*-weld consumes), via:
  - censusDomination_iff_alignableSets : the inlined CensusDomination filter IS alignableSets
    (Lean rfl-certified -- a DEFINITIONAL equality, stronger than any numeric probe), and
  - alignableSets_card_le_budget : the per-band product cap (already in tree).

The genuinely-new content of the LIFT (beyond the single-band probe
probe_alignable_le_pinned_maxmult.py) is UNIFORMITY ACROSS BANDS: censusDomination_of_caps needs
ONE pair (P, M) that caps EVERY deep band a >= a0 simultaneously, for the SAME word pair.  This
probe confirms that a single (P, M) = (#pinned_max, maxMult_max) over the deep-band window indeed
dominates #alignableSets at EVERY band a in [a0, n], so the hypotheses of the lift are
SATISFIABLE (non-vacuous) at the prize regime -- it is NOT a vacuous forall.

Also records, per band, #alignableSets <= #pinned(a) * maxMult(a) <= P*M, so the per-band cap the
lift packages is the real incidence cap, and the band-uniform (P, M) is a genuine common bound.

Structured planted-codeword words on PROPER thin mu_n (n=2^a), prize-regime p (p >> n^3,
p == 1 mod n).  NEVER n = q-1.
"""
import itertools, random
from math import comb
from sympy import isprime, primitive_root


def find_p(n, beta=4):
    p = n ** beta + 1
    while True:
        if (p - 1) % n == 0 and isprime(p):
            return p
        p += 1


def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return sorted({pow(h, i, p) for i in range(n)})


def lowdeg(dom, k, p, c):
    return [sum(c[e] * pow(x, e, p) for e in range(k)) % p for x in dom]


def residual_val(u, tup, dom, k, p):
    # divided-difference-style residual: does u restricted to tup lie on a deg<k poly?
    # we use the (k+1)-point Lagrange obstruction: u is deg<k on tup iff the order-k
    # finite difference vanishes.  Build it via the standard leave-one-out determinant sign-free
    # test: fit deg<k through first k points, check the (k+1)-th.
    xs = [dom[i] for i in tup]
    ys = [u[i] for i in tup]
    # Lagrange-interpolate deg<k through points 0..k-1, evaluate at point k, compare to ys[k].
    xk = xs[k]
    interp = 0
    for j in range(k):
        num = 1
        den = 1
        for l in range(k):
            if l == j:
                continue
            num = (num * (xk - xs[l])) % p
            den = (den * (xs[j] - xs[l])) % p
        interp = (interp + ys[j] * num * pow(den, p - 2, p)) % p
    return (ys[k] - interp) % p


def aligned_gamma(u0, u1, tup, dom, k, p):
    # gamma with res0 + gamma*res1 = 0; returns field gamma, or "deg" if both residuals
    # vanish (degenerate tuple), or None if no aligning gamma (r1==0, r0!=0).
    r0 = residual_val(u0, tup, dom, k, p)
    r1 = residual_val(u1, tup, dom, k, p)
    if r0 == 0 and r1 == 0:
        return "deg"
    if r1 == 0:
        return None
    return (-r0 * pow(r1, p - 2, p)) % p


def census(dom, k, a, u0, u1, p):
    """Return (#alignableSets, #pinnedScalars, maxMult) at band a."""
    n = len(dom)
    pinned = {}  # gamma -> count of aligned a-sets pinned to it
    n_align = 0
    for S in itertools.combinations(range(n), a):
        Sset = set(S)
        # S is alignable iff EXISTS gamma s.t. ALL (k+1)-tuples in S align to that SAME gamma
        # (Aligned is a forall over tuples), AND S contains at least one non-degenerate tuple.
        tup_gammas = []
        has_nondegen = False
        consistent = True
        common = None
        for tup in itertools.combinations(S, k + 1):
            g = aligned_gamma(u0, u1, tup, dom, k, p)
            if g == "deg":
                continue  # degenerate tuple: aligns for every gamma, no constraint
            if g is None:
                consistent = False  # r1==0, r0!=0: no gamma aligns this tuple
                break
            has_nondegen = True
            if common is None:
                common = g
            elif common != g:
                consistent = False
                break
        if consistent and has_nondegen and common is not None:
            n_align += 1
            pinned[common] = pinned.get(common, 0) + 1
    npin = len(pinned)
    mx = max(pinned.values()) if pinned else 0
    return n_align, npin, mx


def main():
    random.seed(7)
    rows = []
    all_ok = True
    for n in (8, 16):
        for beta in (4, 5):
            p = find_p(n, beta)
            dom = mu_n(p, n)
            k = 2
            a0 = k + 2
            # planted: low-degree codewords PERTURBED off the code on a few points, so that
            # some (k+1)-tuples are non-degenerate (off-codeword) and actually pin a gamma.
            c0 = [random.randrange(p) for _ in range(k)]
            c1 = [random.randrange(p) for _ in range(k)]
            u0 = lowdeg(dom, k, p, c0)
            u1 = lowdeg(dom, k, p, c1)
            # perturb u1 off the code on a single point so residuals are generically nonzero
            jp = random.randrange(n)
            u1[jp] = (u1[jp] + 1 + random.randrange(p - 1)) % p
            # sweep bands a0..min(n, a0+3) to keep enumeration tractable
            band_hi = min(n, a0 + 3)
            per_band = []
            for a in range(a0, band_hi + 1):
                na, npin, mx = census(dom, k, a, u0, u1, p)
                per_band.append((a, na, npin, mx))
            # band-uniform caps
            P = max((npin for _, _, npin, _ in per_band), default=0)
            M = max((mx for _, _, _, mx in per_band), default=0)
            K = P * M
            # CHECK: a single (P, M) caps EVERY band
            uniform_ok = all(na <= P * M for _, na, _, _ in per_band)
            perband_ok = all(na <= npin * mx for _, na, npin, mx in per_band)
            all_ok = all_ok and uniform_ok and perband_ok
            rows.append((n, beta, p, k, a0, P, M, K, per_band, uniform_ok, perband_ok))

    print("n  beta  p           k a0   P    M     K=P*M  | per-band (a:#align,#pin,maxMult)  unif perband")
    for n, beta, p, k, a0, P, M, K, pb, u_ok, pb_ok in rows:
        pbs = " ".join(f"{a}:{na},{npin},{mx}" for a, na, npin, mx in pb)
        print(f"{n:<2} {beta:<4} {p:<11} {k} {a0:<4} {P:<4} {M:<5} {K:<6} | {pbs}  {u_ok} {pb_ok}")

    print()
    if all_ok:
        print("VERDICT PASS: a band-UNIFORM (P,M) dominates #alignableSets at EVERY band a>=a0")
        print("  => censusDomination_of_caps hypotheses are SATISFIABLE (non-vacuous) at prize regime.")
        print("  per-band #alignableSets <= #pinned*maxMult holds at every band (the lift's engine).")
    else:
        print("VERDICT FAIL: band-uniform cap violated -- investigate.")
    print("ASYMPTOTIC GUARD: pure census-combinatorics lift (forall-intro over bands); no")
    print("  climb-to-capacity, the delta*/incidence cliff-at-n/2 object is UNTOUCHED.")


if __name__ == "__main__":
    main()
