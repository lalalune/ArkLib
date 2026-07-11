#!/usr/bin/env python3
r"""#407 LANE 4 — GLT push past r=2: the DECISIVE r=3 (V_6) low-weight test (v2).

================================================================================
MISSION (incremental only; asymptotic GLT+Deligne no-go already CONFIRMED).

GLT (arXiv:2112.13886) prove r=2 (4th moment V_4) random-like by reducing the
count to 2-VARIABLE affine diagonal counts c_{i,j,k} = #{a,b in Gamma : a+g^j b=g^k}
— each a CURVE, Hasse-Weil error 2g*sqrt(p) = WEIGHT 1 = p^{1/2}.

THE r=3 QUESTION: does the 6th moment N_3 likewise reduce to a low-weight (curve,
weight 1) model, giving a per-fixed-r=3 in-regime theorem — or does it produce a
genuine weight-2 (surface) error so the low-weight model FAILS at r=3?

================================================================================
THE CORRECT FROBENIUS-ERROR ISOLATION (v2, fixed).

GLT's exact identity for the 2r-th moment (their Thm 3 generalized):
    V_{2r} := sum_a |eta_a|^{2r} = p * N_r,
    N_r = #{(x_1..x_r,y_1..y_r) in mu^{2r} : sum x_i = sum y_j (mod p)}.
We split N_r by WHETHER the common sum s = sum x_i is ZERO or NONZERO:
    N_r = N_r^{s=0} + N_r^{s!=0}.
The KEY object carrying Frobenius eigenvalues is the per-residue count.  For the
GLT curve correspondence, the relevant counts are
    M(t) := #{(x_1..x_r) in mu^r : sum x_i = t}   for t in F_p,
and N_r = sum_t M(t)^2.  Each M(t) for t != 0 is, after a_i=x_i and the d-th-power
substitution, the point count of a DIAGONAL hypersurface
    x_1^d + ... + x_r^d = t' (a fixed scaling)   -- the modified-Fermat variety.
Its MEAN over t!=0 is approx (n^r - [t=0 count]) / (p-1).  The FLUCTUATION
    M(t) - mean
is EXACTLY the Frobenius-trace term, of weight w.  We measure w by the empirical
scaling of the EXACT centered variance of M over the nonzero residues:
    FrobVar := sum_{t!=0} (M(t) - mu1)^2 ,   mu1 = (sum_{t!=0} M(t))/(p-1).
Cohomologically, M(t) = mean + (Frobenius trace of the diagonal hypersurface
x_1^d+...+x_r^d = t), whose trace has |.| <= B * p^{(r-1)/2} (the AFFINE diagonal
in r vars = dim r-1, weight r-1, eigenvalue p^{(r-1)/2}).  So
    FrobVar = sum_{t!=0} (trace_t)^2 ~ (p-1) * (typical trace)^2 ~ p * p^{r-1} = p^r,
i.e. the per-t trace has weight (r-1)/2 and FrobVar has weight r.  That is the
GENERIC envelope.  THE LOW-WEIGHT QUESTION becomes: is the per-t fluctuation
trace_t of weight (r-1)/2 (generic: r=2 -> 1/2 win; r=3 -> 1, a genuine surface
weight-1-per-trace = weight-2-in-variance), or does GLT-style cancellation drop it?

CLEANEST DECISIVE STATISTIC.  Fit  log( max_{t!=0} |M(t) - mu1| )  vs  log p.
  * The MAX single-residue fluctuation IS the Frobenius trace of ONE diagonal
    hypersurface x_1^d+..+x_r^d = t.  Its weight is exactly (dim)/2 = (r-1)/2 for
    the AFFINE diagonal (generic), UNLESS the variety degenerates to lower weight.
  * r=2: affine diagonal x1^d+x2^d=t is a CURVE (dim 1), weight 1/2, max|M-mu|~p^{1/2}.
        This is GLT's curve / sqrt(p).  <-- calibrate to ~0.5.
  * r=3: affine diagonal x1^d+x2^d+x3^d=t is a SURFACE (dim 2), weight 1,
        max|M-mu| ~ p^{1}  IF generic; if a low-weight (curve) model existed it
        would be ~p^{1/2}.  THE TEST: fit the r=3 exponent. >=~0.9 => surface,
        low-weight model FAILS, wall confirmed at r=3.  ~0.5 => curve, win.
================================================================================
"""

from math import log
import json

# ----------------------------------------------------------------- prime helpers
def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    i = 5
    while i * i <= x:
        if x % i == 0 or x % (i + 2) == 0: return False
        i += 6
    return True

def primes_with_index(d, n_lo, n_hi):
    out = []
    for n in range(n_lo, n_hi + 1):
        p = d * n + 1
        if isprime(p):
            out.append((p, n))
    return out

def subgroup_mu_n(p, d):
    n = (p - 1) // d
    S = set(pow(x, d, p) for x in range(1, p))
    assert len(S) == n, (p, d, len(S), n)
    return sorted(S), n

# ----------------------------------------------------------------- M(t) distribution
def sum_distribution(p, mu, r):
    r"""M[t] = #{(x_1..x_r) in mu^r : x_1+...+x_r == t (mod p)}, via r-fold convolution."""
    f = [0] * p
    for x in mu:
        f[x] += 1
    M = f[:]
    for _ in range(r - 1):
        nM = [0] * p
        for s in range(p):
            v = M[s]
            if v:
                for x in mu:
                    nM[(s + x) % p] += v
        M = nM
    return M

# ----------------------------------------------------------------- Frobenius statistics
def frobenius_stats(p, M):
    r"""Centered fluctuation of M over the NONZERO residues t != 0.
    Returns (mu1, max_abs_dev, frob_var, M0)."""
    M0 = M[0]
    nz = [M[t] for t in range(1, p)]
    s = sum(nz)
    mu1 = s / (p - 1)
    devs = [m - mu1 for m in nz]
    max_abs = max(abs(dv) for dv in devs)
    frob_var = sum(dv * dv for dv in devs)
    return mu1, max_abs, frob_var, M0

def linfit(pairs):
    """slope of y ~ a + b x (least squares), b returned."""
    if len(pairs) < 3: return None
    xs = [a for a, _ in pairs]; ys = [b for _, b in pairs]
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    den = sum((x - mx) ** 2 for x in xs)
    if den == 0: return None
    return sum((x - mx) * (y - my) for x, y in pairs) / den

# ----------------------------------------------------------------- main
def main():
    print("=" * 92)
    print("#407 LANE 4 — GLT r=3 (V_6) low-weight test v2: weight of the per-residue Frobenius trace")
    print("=" * 92)
    print("""
Per-residue count M(t) = #{x_1+..+x_r = t, x_i in mu_n} = mean + Frobenius_trace(t).
trace(t) = trace of the AFFINE diagonal x_1^d+..+x_r^d = t', dim r-1, generic weight (r-1)/2.
  r=2 -> curve, weight 1/2, max|M-mu| ~ p^{0.5}   (GLT's sqrt(p); calibration)
  r=3 -> surface, weight 1,  max|M-mu| ~ p^{1.0}   IF generic; ~p^{0.5} IF low-weight model
DECISIVE: fit exponent of max_{t!=0}|M(t)-mu1| vs p.  ~0.5 = curve/win; ~1.0 = surface/wall.
""")
    results = {"per_d": {}}
    summary = []
    for d in (3, 4, 5, 6):
        plist = primes_with_index(d, 4, 280)
        plist = [(p, n) for (p, n) in plist if p <= 1700 and n >= 4]
        print(f"--- index d={d}: {len(plist)} primes p=d*n+1 (4<=n, p<=1700) ---")
        rowsbyr = {}
        for r in (2, 3):
            pairs_max, pairs_var = [], []
            for (p, n) in plist:
                mu, nn = subgroup_mu_n(p, d)
                M = sum_distribution(p, mu, r)
                mu1, max_abs, frob_var, M0 = frobenius_stats(p, M)
                if max_abs > 1.5:
                    pairs_max.append((log(p), log(max_abs)))
                if frob_var > 1.5:
                    pairs_var.append((log(p), log(frob_var)))
            w_max = linfit(pairs_max)
            w_var = linfit(pairs_var)
            rowsbyr[r] = {"w_max": w_max, "w_var": w_var,
                          "n_primes": len(plist),
                          "expected_generic_w_max": (r - 1) / 2,
                          "expected_generic_w_var": r - 1}
            print(f"  r={r}: fitted weight of max|M-mu| = {w_max:.4f}  "
                  f"(generic (r-1)/2 = {(r-1)/2});  "
                  f"weight of FrobVar = {w_var:.4f}  (generic r-1 = {r-1})")
        results["per_d"][d] = rowsbyr
        # verdict for this d
        w2 = rowsbyr[2]["w_max"]; w3 = rowsbyr[3]["w_max"]
        summary.append((d, w2, w3))
        print(f"    VERDICT d={d}: r=2 max-dev exponent {w2:.3f} (expect 0.5, GLT curve); "
              f"r=3 max-dev exponent {w3:.3f}")
        if w3 is not None:
            if w3 >= 0.85:
                print(f"            => r=3 ~ p^1 : GENUINE SURFACE (weight 1), low-weight model FAILS.")
            elif w3 <= 0.6:
                print(f"            => r=3 ~ p^0.5 : CURVE-LEVEL, low-weight model SURVIVES (would be a win!).")
            else:
                print(f"            => r=3 intermediate {w3:.3f} : ambiguous, finite-size effects.")
        print()

    print("=" * 92)
    print("CROSS-INDEX SUMMARY  (max-dev exponent = weight of per-residue Frobenius trace)")
    print("=" * 92)
    print(f"  {'d':>4} {'r=2 (GLT curve, ~0.5)':>24} {'r=3 (test, ~1.0=surface)':>26}")
    for d, w2, w3 in summary:
        print(f"  {d:>4} {w2:>24.4f} {w3:>26.4f}")
    avg_w3 = sum(w3 for _, _, w3 in summary if w3) / len([1 for _, _, w3 in summary if w3])
    avg_w2 = sum(w2 for _, w2, _ in summary if w2) / len([1 for _, w2, _ in summary if w2])
    print(f"\n  AVERAGE r=2 max-dev exponent = {avg_w2:.4f}  (GLT predicts 0.5: the genus-(d-1)(d-2)/2 curve)")
    print(f"  AVERAGE r=3 max-dev exponent = {avg_w3:.4f}  (generic surface predicts 1.0)")
    results["summary"] = {"avg_w2_maxdev": avg_w2, "avg_w3_maxdev": avg_w3,
                          "per_d_summary": summary}

    print(f"""
================================================================================
VERDICT
================================================================================
GLT r=2 reduces to a genus-(d-1)(d-2)/2 CURVE: per-residue M(t) fluctuation has
weight 1/2 (error sqrt(p)).  Measured r=2 exponent ~ {avg_w2:.3f} (target 0.5).

r=3: the per-residue count M(t)=#{{x1+x2+x3=t, xi in mu_n}} is the point count of
the AFFINE diagonal SURFACE x1^d+x2^d+x3^d = t' (dimension 2).  Its primitive
middle cohomology is H^2, weight 2, Frobenius eigenvalues of absolute value p^1.
Measured r=3 exponent ~ {avg_w3:.3f}.

  * If ~ 1.0: the low-weight (curve) model FAILS at r=3.  The 6th-moment error is
    genuinely WEIGHT 2 (surface-level), p^1 per residue, n^3 in the full variance.
    GLT's curve method does NOT extend: there is NO genus reduction for the
    3-summand diagonal.  An incremental per-fixed-r=3 in-regime sqrt-power theorem
    does NOT exist via this route — the Betti/weight is intrinsically too high.
================================================================================""")

    out = "/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes/glt_r3_results.json"
    with open(out, "w") as f:
        json.dump(results, f, indent=1, default=str)
    print(f"[written] {out}")

if __name__ == "__main__":
    main()
