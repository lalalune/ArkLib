#!/usr/bin/env python3
r"""
probe_moment_optimum_vs_floor.py  (#334 proximity-prize floor / char-p Gauss-period transfer)

THE SHARPER QUESTION (successor to probe_ktransfer_deeptail_decisive.py).

BACKGROUND
----------
The proximity-prize delta* floor reduces (via the moment method) to a char-p
Gauss-period sup-norm bound

        M(n) = max_{b != 0} |eta_b|,    eta_b = sum_{x in mu_n} e_p(b x),  e_p(t)=exp(2*pi*i*t/p),

over the 2-power multiplicative subgroup mu_n  (n = 2^mu, n | p-1, index m = (p-1)/n).
The TARGET floor is the square-root-log law

        F(n) = sqrt( 2 * n * ln m ),      m = (p-1)/n,

i.e. M(n) = O( sqrt(n * log m) ) = O( sqrt(n * (beta-1) * log n) ) at p ~ n^beta.

THE MOMENT METHOD (the route under test).
The EXACT moment identity is

        E_r^{(p)}(mu_n) = (1/p) * sum_{b in F_p} |eta_b|^{2r}                       (*)

(E_r = the r-th ADDITIVE energy of mu_n over F_p; see probe_ktransfer_deeptail_decisive.py).
Dropping all but the b=0 term (eta_0 = n) and the maximizing b gives, for EVERY depth r,

        p * E_r^{(p)} >= |eta_0|^{2r} + M^{2r} = n^{2r} + M^{2r}     =>     M^{2r} <= p * E_r^{(p)},

hence the per-depth moment bound and its optimum

        M_bound(r) := ( p * E_r^{(p)} )^{1/(2r)},     M_bound* := min_r M_bound(r).

(We use q = p as the multiplier, matching M^{2r} <= q * E_r with q = field size = p.
 We also report the strictly-better-but-same-order variant ( p*E_r - n^{2r} )^{1/(2r)}.)

THE DECISIVE PRIOR RESULT (probe_ktransfer_deeptail_decisive.py, commit 50a1ffdac):
the anomaly ratio R(r) = (E_r^{(p)}/Wick_r)^{1/r}, Wick_r=(2r-1)!! n^r, CROSSES 1 with an
onset depth that SHRINKS as n grows  => the *bounded-K* (DC-Wick) hypothesis FAILS at beta=4.

THE SUBTLE RESIDUAL QUESTION this probe settles with numbers:
bounded-K failing does NOT by itself mean the OPTIMIZED moment bound min_r (p*E_r)^{1/(2r)}
misses the floor.  Maybe the optimal depth r* sits BELOW the R>1 onset, so M_bound* still
lands at ~ sqrt(n log m).  We measure, exactly where feasible:

  (a) the optimal depth r* = argmin_r M_bound(r), and whether r* is BELOW or ABOVE the
      R(r)>1 anomaly-onset depth;
  (b) whether M_bound*/F(n) stays BOUNDED (moment method delivers the floor up to a constant)
      or GROWS with n (moment method overshoots the floor);
  (c) the TRUE M(n)/sqrt(n) (the sqrt-log excess) vs M_bound*/sqrt(n) -- is the moment bound
      even close to the truth, or hugely loose?

EXACTNESS / HONESTY
-------------------
* E_r^{(p)}(mu_n): EXACT integer counts, reused verbatim (int64 cyclic convolution mod p,
  Python-int sum of squares) from probe_ktransfer_deeptail_decisive.py.  Every E_r is a
  certified count; the depth sweep stops before any int64 count overflows 2^62.
* TRUE M(n) = max_{b!=0}|eta_b|: computed DIRECTLY.  eta_b depends only on the coset b*mu_n,
  so there are exactly m = (p-1)/n distinct values; we enumerate one representative per coset
  and evaluate eta_b = sum_{x in mu_n} exp(2*pi*i*b*x/p) in float64 (vectorized).  The
  magnitudes are O(sqrt(n log m)) ~ O(20), far inside float64's ~15-digit precision; this is
  "exact-ish" (high precision, not arbitrary precision) and we SAY SO.  Cross-check: the EXACT
  Parseval identity sum_{b!=0} |eta_b|^2 = E_1*p - n^2 = n(p-1) - n^2 = n(p-n) must hold; we
  print the relative error of the directly-summed value as a precision certificate, and we
  verify M(n)^{2r} <= p*E_r^{(p)} (the bound must dominate the truth) at every depth.
* The honest scale ceiling at beta=4 (p ~ n^4): n=16 (p~6.6e4), n=32 (p~1.0e6), n=64 (p~1.7e7)
  are exact and fast; n=128 (p~2.7e8, ~2 GB int64 + ~2.7e8 coset scan) only with ALLOW_N128=1.
  We report the scale actually reached; no extrapolation is labeled as measurement.

Reproducible.  No fabrication.
"""

import os
import sys
import math
import time
import numpy as np


# ----------------------------------------------------------------------------
# number theory helpers (exact) -- identical to the decisive probe
# ----------------------------------------------------------------------------
def isprime(x):
    if x < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % p == 0:
            return x == p
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, d, x)
        if y == 1 or y == x - 1:
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def factorize(x):
    f = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        f[x] = f.get(x, 0) + 1
    return f


def primitive_root(p):
    fs = set(factorize(p - 1))
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def v2(x):
    s = 0
    while x % 2 == 0:
        x //= 2
        s += 1
    return s


def smallest_prime_at_beta(n, beta):
    """Smallest prime p >= n^beta with p == 1 (mod n) and v2(p-1) >= log2(n)."""
    mu = int(round(math.log2(n)))
    step = n
    lo = int(math.floor(n ** beta))
    p = (lo // step) * step + 1
    if p < lo:
        p += step
    while True:
        if (p - 1) % n == 0 and v2(p - 1) >= mu and isprime(p):
            return p
        p += step


def double_factorial_odd(r):
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


# ----------------------------------------------------------------------------
# EXACT char-p additive energies E_r^{(p)}(mu_n) -- reused from the decisive probe
# ----------------------------------------------------------------------------
def Er_charp_exact(p, n, R):
    """dict r -> E_r^{(p)}(mu_n) (exact Python int), maxN[r], and the roots of mu_n."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    roots = sorted(set(pow(h, i, p) for i in range(n)))
    assert len(roots) == n, f"mu_n not full: {len(roots)} != {n}"

    N = np.zeros(p, dtype=np.int64)
    for x in roots:
        N[x] += 1

    out = {}
    maxN = {}
    INT64_GUARD = 1 << 62

    for r in range(1, R + 1):
        if r > 1:
            acc = np.zeros(p, dtype=np.int64)
            for x in roots:
                acc += np.roll(N, int(x))
            N = acc
            mx = int(N.max())
            if mx >= INT64_GUARD:
                raise OverflowError(
                    f"int64 overflow risk at r={r}: max count {mx} >= 2^62")
            maxN[r] = mx
        else:
            maxN[r] = int(N.max())
        Nsq = N.astype(object)
        out[r] = int(np.sum(Nsq * Nsq))
    return out, maxN, roots


# ----------------------------------------------------------------------------
# TRUE M(n) = max_{b != 0} |eta_b|  via the coset structure (high precision float64)
# ----------------------------------------------------------------------------
def true_M_and_parseval(p, n, roots):
    """Compute eta_b for one representative b per coset of mu_n in F_p^*, return
    (M, parseval_rel_err, m).  m = (p-1)/n distinct |eta_b| values (b!=0).

    eta_b depends only on the coset b*mu_n: if b' = b*z for z in mu_n then the map
    x -> z*x permutes mu_n, so {b'x} = {b x} as multisets in F_p, hence eta_{b'}=eta_b.
    So we scan coset reps only: cost m*n complex exponentials (vs (p-1)*n for all b).

    Precision certificate: the EXACT Parseval identity is
        sum_{b!=0} |eta_b|^2 = sum_{all b}|eta_b|^2 - eta_0^2 = p*E_1 - n^2 = n(p-1) - n^2,
    and since each coset contributes n equal terms,
        n * sum_{coset reps c} |eta_c|^2 = n(p-1) - n^2  =>  sum_c |eta_c|^2 = (p-1) - n = p-1-n.
    We compare the directly-summed LHS to this exact RHS and report the relative error.
    """
    g = primitive_root(p)
    # coset reps: g^j for j = 0..m-1 are a transversal of mu_n = <g^m> in F_p^* = <g>.
    m = (p - 1) // n
    reps = np.empty(m, dtype=np.int64)
    cur = 1
    for j in range(m):
        reps[j] = cur
        cur = (cur * g) % p
    roots_arr = np.asarray(roots, dtype=np.float64)  # the n roots as residues in [0,p)

    # eta_c = sum_{x in mu_n} exp(2*pi*i * c*x / p).  Vectorize over coset reps in chunks
    # to bound memory: outer product (chunk x n) of phases.
    two_pi_over_p = 2.0 * math.pi / p
    M = 0.0
    parseval = 0.0
    CHUNK = max(1, min(m, 1 << 20))  # cap chunk*n complex doubles in memory
    # ensure chunk*n stays modest (<~ 1.5e8 doubles)
    while CHUNK * n > (1 << 27):
        CHUNK //= 2
        if CHUNK < 1:
            CHUNK = 1
            break
    for start in range(0, m, CHUNK):
        end = min(m, start + CHUNK)
        c = reps[start:end].astype(np.float64)             # (k,)
        # phase[k, x] = c_k * root_x  mod p  -> angle = 2pi/p * (c_k*root_x mod p)
        # do the product in float64 then reduce mod p exactly via int64 to avoid loss:
        prod = (reps[start:end][:, None].astype(np.int64) *
                np.asarray(roots, dtype=np.int64)[None, :]) % p   # (k, n) exact residues
        ang = two_pi_over_p * prod.astype(np.float64)
        re = np.cos(ang).sum(axis=1)
        im = np.sin(ang).sum(axis=1)
        mag2 = re * re + im * im
        parseval += float(mag2.sum())
        mloc = float(np.sqrt(mag2.max()))
        if mloc > M:
            M = mloc
    parseval_exact = float(p - 1 - n)   # sum over coset reps of |eta_c|^2
    rel_err = abs(parseval - parseval_exact) / parseval_exact if parseval_exact else float('nan')
    return M, rel_err, m


# ----------------------------------------------------------------------------
# main analysis per (n, beta)
# ----------------------------------------------------------------------------
def analyze(n, beta, Rmax):
    p = smallest_prime_at_beta(n, beta)
    beta_actual = math.log(p) / math.log(n)
    m = (p - 1) // n
    F = math.sqrt(2.0 * n * math.log(m))            # target sqrt-log floor
    sqrt_n = math.sqrt(n)
    parseval_anchor = math.sqrt(n * (p - n) / (p - 1))  # RMS of |eta_b| over b!=0 (~sqrt(n))

    print("=" * 110)
    print(f"### n={n}  beta_target={beta}  p={p}  (beta_actual={beta_actual:.3f})  "
          f"m=(p-1)/n={m}")
    print(f"    target floor F(n)=sqrt(2 n ln m) = {F:.4f}   sqrt(n)={sqrt_n:.4f}   "
          f"Parseval RMS anchor sqrt(n(p-n)/(p-1)) = {parseval_anchor:.4f}")
    print("=" * 110)

    # --- EXACT char-p energies ---
    t0 = time.time()
    try:
        Er, maxN, roots = Er_charp_exact(p, n, Rmax)
    except OverflowError as e:
        print(f"    [ABORTED energy sweep: {e}]")
        return None
    t_energy = time.time() - t0

    # --- TRUE M(n) directly ---
    t1 = time.time()
    M_true, parseval_rel_err, _ = true_M_and_parseval(p, n, roots)
    t_M = time.time() - t1
    print(f"    TRUE M(n) = max_{{b!=0}}|eta_b| = {M_true:.6f}   "
          f"(direct coset scan over m={m} reps, {t_M:.1f}s; "
          f"Parseval rel-err = {parseval_rel_err:.2e} -- precision certificate)")
    print(f"    [exact char-p energies E_1..E_{Rmax} computed in {t_energy:.1f}s]")
    print()

    # --- per-depth moment bound table ---
    print(f"    {'r':>3} | {'E_r^(p) (EXACT)':>22} | {'M_bound(r)=(p E_r)^(1/2r)':>26} | "
          f"{'(pE_r-n^2r)^(1/2r)':>20} | {'R(r)=(E_r/Wick)^1/r':>20} | bound>=M?")
    rows = []
    onset = None
    for r in range(1, Rmax + 1):
        pEr = p * Er[r]
        Mb = pEr ** (1.0 / (2 * r))
        sub = pEr - n ** (2 * r)
        Mb_sub = (sub ** (1.0 / (2 * r))) if sub > 0 else float('nan')
        Wick = double_factorial_odd(r) * (n ** r)
        Rr = (Er[r] / Wick) ** (1.0 / r)
        if r >= 2 and Rr > 1.0 and onset is None:
            onset = r
        bound_ok = (M_true ** (2 * r)) <= pEr * (1 + 1e-9)
        rows.append((r, Er[r], Mb, Mb_sub, Rr, bound_ok))
        print(f"    {r:>3} | {Er[r]:>22d} | {Mb:>26.5f} | {Mb_sub:>20.5f} | "
              f"{Rr:>20.5f} | {'yes' if bound_ok else 'NO!!':>8}")

    # --- optimum ---
    r_star = min(rows, key=lambda t: t[2])[0]
    Mb_star = min(t[2] for t in rows)
    # sub-variant optimum (ignoring nan)
    sub_rows = [(t[0], t[3]) for t in rows if t[3] == t[3]]  # filter nan
    r_star_sub, Mb_star_sub = (min(sub_rows, key=lambda t: t[1]) if sub_rows
                               else (None, float('nan')))

    print()
    print(f"    OPTIMUM:  r* = argmin_r M_bound(r) = {r_star}   M_bound* = {Mb_star:.5f}")
    print(f"              (sub-variant r*_sub={r_star_sub}, M_bound*_sub={Mb_star_sub:.5f})")
    print(f"    R(r)>1 anomaly ONSET depth = {onset}   "
          f"=>  r* is {'BELOW' if (onset is None or r_star < onset) else 'AT/ABOVE'} the onset"
          + (f" (onset r={onset})" if onset else " (no onset within computed depths)"))
    print()
    print(f"    RATIOS (the decisive numbers):")
    print(f"      true M(n)          = {M_true:.4f}")
    print(f"      M_bound*           = {Mb_star:.4f}")
    print(f"      floor F(n)         = {F:.4f}")
    print(f"      M_bound* / F(n)    = {Mb_star / F:.4f}      <-- BOUNDED across n? (route gives floor up to const)")
    print(f"      true M(n) / F(n)   = {M_true / F:.4f}      <-- truth already <= floor (sanity)")
    print(f"      M_bound* / sqrt(n) = {Mb_star / sqrt_n:.4f}")
    print(f"      true M(n) / sqrt(n)= {M_true / sqrt_n:.4f}      <-- the genuine sqrt-log excess")
    print(f"      M_bound* / M_true  = {Mb_star / M_true:.4f}      <-- how loose the (optimized) moment bound is")
    print(flush=True)

    return {
        "n": n, "beta": beta, "p": p, "m": m, "F": F, "sqrt_n": sqrt_n,
        "M_true": M_true, "parseval_rel_err": parseval_rel_err,
        "r_star": r_star, "Mb_star": Mb_star, "onset": onset,
        "Er": Er, "rows": rows,
    }


def main():
    print("#" * 110)
    print("MOMENT OPTIMUM vs PRIZE FLOOR  (beta=4 prize regime, EXACT energies + direct true M(n))")
    print("Question: does M_bound* = min_r (p E_r^(p))^{1/2r} hit the floor F(n)=sqrt(2 n ln m),")
    print("or does the optimum ALSO overshoot (route dead even optimized)? And is r* below the R>1 onset?")
    print("#" * 110)
    print()

    # beta=4, deepest exact r per n (same int64-safe caps as the decisive probe).
    sweep = [
        (16, 4, 18),
        (32, 4, 16),
        (64, 4, 14),
    ]
    if os.environ.get("ALLOW_N128"):
        sweep.append((128, 4, 9))

    results = []
    for n, beta, Rmax in sweep:
        res = analyze(n, beta, Rmax)
        if res:
            results.append(res)

    # ---------------- cross-n synthesis tables ----------------
    print("#" * 110)
    print("CROSS-n SYNTHESIS (beta=4)")
    print("#" * 110)
    print()
    print(f"  {'n':>5} | {'p':>11} | {'m':>9} | {'r*':>4} | {'onset':>6} | "
          f"{'M_bound*':>10} | {'true M':>8} | {'F(n)':>8} | "
          f"{'Mb*/F':>7} | {'M/F':>6} | {'Mb*/sqn':>8} | {'M/sqn':>7} | {'Mb*/M':>7}")
    for r in results:
        on = r["onset"]
        print(f"  {r['n']:>5} | {r['p']:>11} | {r['m']:>9} | {r['r_star']:>4} | "
              f"{(str(on) if on else '-'):>6} | "
              f"{r['Mb_star']:>10.4f} | {r['M_true']:>8.4f} | {r['F']:>8.4f} | "
              f"{r['Mb_star']/r['F']:>7.4f} | {r['M_true']/r['F']:>6.4f} | "
              f"{r['Mb_star']/r['sqrt_n']:>8.4f} | {r['M_true']/r['sqrt_n']:>7.4f} | "
              f"{r['Mb_star']/r['M_true']:>7.4f}")
    print()

    # growth diagnostics
    if len(results) >= 2:
        print("  GROWTH across n (is the ratio bounded or growing as n: 16->32->64 ...):")
        seq_MbF = [r["Mb_star"] / r["F"] for r in results]
        seq_MF = [r["M_true"] / r["F"] for r in results]
        seq_loose = [r["Mb_star"] / r["M_true"] for r in results]
        ns = [r["n"] for r in results]
        print(f"    M_bound*/F(n) :  " + "  ".join(f"n={ns[i]}:{seq_MbF[i]:.4f}" for i in range(len(ns))))
        print(f"    true M/F(n)   :  " + "  ".join(f"n={ns[i]}:{seq_MF[i]:.4f}" for i in range(len(ns))))
        print(f"    M_bound*/M    :  " + "  ".join(f"n={ns[i]}:{seq_loose[i]:.4f}" for i in range(len(ns))))
        # crude per-octave growth factor
        def growth(seq):
            return [seq[i+1] / seq[i] for i in range(len(seq) - 1)]
        print(f"    per-octave factor M_bound*/F:  {['%.3f'%x for x in growth(seq_MbF)]}")
        print(f"    per-octave factor M_bound*/M:  {['%.3f'%x for x in growth(seq_loose)]}")
    print()

    # ---------------- verdict ----------------
    print("#" * 110)
    print("VERDICT")
    print("#" * 110)
    print("""
  READING GUIDE:
   * If M_bound*/F(n) stays BOUNDED (roughly constant) as n grows, the OPTIMIZED moment
     method delivers M <= O(sqrt(n log m)) at beta=4 -- the route survives despite the
     bounded-K anomaly (the optimal depth r* sits below the R>1 onset and the floor follows).
   * If M_bound*/F(n) GROWS with n, the optimum ALSO overshoots the floor: the moment
     route is dead even when fully optimized over depth (not merely at bounded fixed K).
   * true M(n)/sqrt(n) is the genuine sqrt-log excess of the actual sup-norm; M_bound*/M
     measures how loose the best moment bound is relative to the truth.
""")
    if len(results) >= 2:
        ratios = [r["Mb_star"] / r["F"] for r in results]
        grew = all(ratios[i+1] > ratios[i] * 1.02 for i in range(len(ratios) - 1))
        flat = max(ratios) / min(ratios) < 1.15
        ns = [r["n"] for r in results]
        below = all((r["onset"] is None) or (r["r_star"] < r["onset"]) for r in results)
        print(f"  MEASURED (this run, beta=4, n in {ns}):")
        print(f"    r* {'IS' if below else 'is NOT always'} below the R(r)>1 onset depth.")
        print(f"    M_bound*/F(n) sequence = {['%.4f'%x for x in ratios]}")
        if grew:
            print("    => M_bound*/F(n) GROWS with n  =>  the OPTIMIZED moment bound OVERSHOOTS the")
            print("       floor; the DC-Wick/moment route is DEAD even optimized over depth at beta=4.")
        elif flat:
            print("    => M_bound*/F(n) is ~FLAT  =>  the optimized moment bound TRACKS the floor")
            print("       up to a constant; the route survives optimization at the scales reached.")
        else:
            print("    => M_bound*/F(n) neither clearly flat nor clearly growing at these scales;")
            print("       read the per-octave factors and push to larger n.")
        print(f"    Scale reached EXACTLY: n in {ns} (beta=4, p~n^4); n>=128 only with ALLOW_N128=1.")
    print()
    print("DONE", flush=True)


if __name__ == "__main__":
    main()
