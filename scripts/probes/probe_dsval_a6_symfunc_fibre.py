#!/usr/bin/env python3
"""
A6 SYMMETRIC-FUNCTION FIBRE -- #407 open value delta*(n,rho).

ANGLE. For the far monomial direction (a,b), a<b, a bad scalar gamma realizes
  x^a + gamma*x^b  ==  g(x)   on a w-subset S of mu_n,  g of degree < k.
Equivalently h(x) := x^a + gamma*x^b - g(x) is a polynomial of degree b whose
zero set contains S. The TOP segment (degrees k..b) of h is unconstrained only at
a and b; the consumer pins gamma. In the SIMPLEST binding case b-a corresponds to
the two free top coefficients and gamma is determined by Vieta from S.

CLAIM TO TEST (A6). When the binding band makes h(x) = (monic, deg b) factor as
  h(x) = prod_{s in S}(x - x_s) * r(x),  with r of degree b-w,
the scalar gamma is a SYMMETRIC FUNCTION of the chosen subset. In the cleanest
"two-term" band (b = a+1 step, w = b, so r is constant), gamma = -e_1(S')/... .
We DIRECTLY compute, exactly in char 0 over Z[zeta_n] (n=2^a), the incidence
  I(delta) = #distinct gamma over consistent S
AND the fibre count #distinct e_1 over those S, and check the identity
  gamma  <->  e_1  (Vieta) and whether #distinct e_1 has a closed form.

We do NOT trust a guessed band; we recompute the TRUE consistency via exact
projection-residual collinearity (same predicate as probe_overdet_deltastar_char0)
and then TAG each consistent (S, gamma) with its e_1(S) and other e_j(S), to see
which symmetric function indexes the fibre and whether it is closed-form.

HONESTY: exact char-0 (numpy complex with tight tol + Z[zeta] cross-check on
e_1 distinctness). Proper subgroup mu_n, n=2^a. Tags: proven / conjecture / refuted.
"""
import itertools, cmath, math
import numpy as np
from collections import defaultdict, Counter
from fractions import Fraction

TAU = 2*math.pi

# ----- exact Z[zeta_n] arithmetic (n=2^a), basis 1..zeta^{n/2-1}, zeta^{n/2}=-1 -----
def zroot(j, n):
    half = n//2; e = j % n; v = [0]*half
    if e < half: v[e] = 1
    else: v[e-half] = -1
    return tuple(v)
def zadd(u, v): return tuple(a+b for a, b in zip(u, v))
def zsum_subset(S, n):
    half = n//2; acc = [0]*half
    for j in S:
        r = zroot(j, n)
        for i in range(half): acc[i] += r[i]
    return tuple(acc)
def zmul(u, v, n):
    half = n//2; res = [0]*(2*half)
    for i in range(half):
        if u[i] == 0: continue
        for j in range(half):
            res[i+j] += u[i]*v[j]
    out = [0]*half
    for d in range(2*half):
        c = res[d]
        if c == 0: continue
        dd = d % n
        if dd < half: out[dd] += c
        else: out[dd-half] -= c
    return tuple(out)

def exact_e1_set(S, n):
    """e_1(S) = sum of zeta^s, s in S, exactly in Z[zeta_n]."""
    return zsum_subset(S, n)

# ----- consistency predicate (exact char-0, numpy) -----
def consistent_gamma(n, k, a, b, S):
    """If x^a+gamma*x^b agrees with a deg<k poly on S for a unique gamma, return that
    gamma (complex, rounded); else None. Uses projection-residual collinearity."""
    xs = [cmath.exp(1j*TAU*s/n) for s in S]
    V = np.array([[x**c for c in range(k)] for x in xs], dtype=complex)
    va = np.array([x**a for x in xs], dtype=complex)
    vb = np.array([x**b for x in xs], dtype=complex)
    Vp = np.linalg.pinv(V)
    ra = va - V@(Vp@va); rb = vb - V@(Vp@vb)
    na = np.linalg.norm(ra); nb = np.linalg.norm(rb)
    if nb < 1e-9: return None
    if na < 1e-9: return 0j
    lam = np.vdot(rb, ra)/np.vdot(rb, rb)
    if np.linalg.norm(ra - lam*rb) < 1e-6*na:
        return -lam
    return None

def incidence_and_fibre(n, k, a, b, w):
    """Return (#distinct gamma, list of (gamma_rounded, S, e1_exact))."""
    rec = []
    for S in itertools.combinations(range(n), w):
        g = consistent_gamma(n, k, a, b, S)
        if g is None: continue
        gr = round(g.real, 4) + 1j*round(g.imag, 4)
        rec.append((gr, S, exact_e1_set(S, n)))
    gammas = set(r[0] for r in rec)
    return len(gammas), rec

def vieta_check(rec, n):
    """For each consistent (gamma,S), test the A6 Vieta identity gamma = -e_1(S)
    (mapped to complex). Report fraction matching, and the gamma<->e1 fibre map."""
    half = n//2
    def z_to_c(v):
        return sum(v[i]*cmath.exp(1j*TAU*i/n) for i in range(half))
    match = 0; total = 0
    gamma_for_e1 = defaultdict(set)  # e1 -> set of gammas (is e1 a function of gamma?)
    e1_for_gamma = defaultdict(set)  # gamma -> set of e1 (is gamma a function of e1?)
    for gr, S, e1 in rec:
        total += 1
        ce1 = z_to_c(e1)
        if abs(gr - (-ce1)) < 1e-3: match += 1
        gamma_for_e1[e1].add(gr)
        e1_for_gamma[gr].add(e1)
    # distinct e1 count, and whether the e1->gamma map is injective both ways
    distinct_e1 = len(gamma_for_e1)
    inj_e1_to_gamma = all(len(v) == 1 for v in gamma_for_e1.values())
    inj_gamma_to_e1 = all(len(v) == 1 for v in e1_for_gamma.values())
    return match, total, distinct_e1, inj_e1_to_gamma, inj_gamma_to_e1

def worst_dir_band(n, k):
    """Replicate the master: worst-direction binding band + its incidence, but ALSO
    report the e1 fibre at that band."""
    budget = n
    fars = list(range(k, n))
    best_ds = 1.0; best = None
    for a, b in itertools.combinations(fars, 2):
        ds = None; bandw = None; bandI = None
        for w in range(k+1, n):
            I, _ = incidence_and_fibre(n, k, a, b, w)
            if I <= budget:
                ds = 1 - w/n; bandw = w; bandI = I; break
        if ds is not None and ds < best_ds:
            best_ds = ds; best = (a, b, bandw, bandI)
    return best_ds, best

def main():
    print("="*84)
    print("A6 SYMMETRIC-FUNCTION FIBRE: gamma = -e_1(S) (Vieta) and #distinct e_1 fibre")
    print("="*84)
    for (n, k) in [(8, 2), (8, 4), (16, 4), (16, 8)]:
        rho = k/n
        ds, best = worst_dir_band(n, k)
        if best is None:
            print(f"n={n} k={k}: no binding band <= budget"); continue
        a, b, w, I = best
        print(f"\nn={n} k={k} rho={rho}: WORST delta*={ds:.4f} dir=({a},{b}) "
              f"binding w={w} I={I}")
        # At the binding band, compute the e1 fibre EXACTLY.
        Ig, rec = incidence_and_fibre(n, k, a, b, w)
        match, total, de1, inj_eg, inj_ge = vieta_check(rec, n)
        print(f"   consistent (S,gamma): {total};  #distinct gamma={Ig};  #distinct e_1={de1}")
        print(f"   Vieta gamma=-e_1 holds: {match}/{total}"
              f"  | e1->gamma injective: {inj_eg} | gamma->e1 injective: {inj_ge}")
        # Closed-form candidates for #distinct e_1 / incidence:
        for cand, val in [("n/4-1", n//4-1), ("n/2-1", n//2-1), ("n-2w+...", None),
                          ("w", w), ("n-w", n-w), ("binom(n/2,?)", None)]:
            if val is not None and val == Ig:
                print(f"   >> incidence {Ig} == {cand}")
        # Full incidence profile across all bands for this worst direction:
        print(f"   FULL profile dir=({a},{b}):")
        for ww in range(k+1, n):
            Iw, recw = incidence_and_fibre(n, k, a, b, ww)
            _, tot, de1w, _, _ = vieta_check(recw, n)
            mark = " <=budget" if Iw <= n else ""
            print(f"      w={ww} delta={1-ww/n:.3f}: I={Iw} #e1={de1w} (consistent {tot}){mark}")
    print("\n" + "="*84)
    print("FIBRE-INDEX SWEEP: which e_j indexes the bad-gamma fibre across directions")
    print("="*84)
    # For a FIXED n,k sweep all far directions at a fixed band and report, per direction,
    # the relation between gamma and e_1,...,e_min(k+?) symmetric functions.
    n, k = 16, 4
    for (a, b) in [(4, 6), (4, 5), (4, 8), (5, 7)]:
        for w in [k+1, k+2, k+3]:
            Ig, rec = incidence_and_fibre(n, k, a, b, w)
            if not rec: continue
            match, total, de1, inj_eg, inj_ge = vieta_check(rec, n)
            print(f"  dir=({a},{b}) w={w}: I={Ig} #e1={de1} "
                  f"Vieta={match}/{total} e1<->gamma bij={inj_eg and inj_ge}")
    print("\nDONE")

if __name__ == "__main__":
    main()
