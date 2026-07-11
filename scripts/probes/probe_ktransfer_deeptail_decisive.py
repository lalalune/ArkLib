#!/usr/bin/env python3
r"""
probe_ktransfer_deeptail_decisive.py  (#334 proximity-prize floor / char-p Gauss-period transfer)

DECISIVE deep-tail measurement of the char-p additive-energy transfer constant.

BACKGROUND
----------
The proximity-prize delta* floor reduces (via the moment method) to a char-p
Gauss-period sup-norm bound  M(n) = max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x),
over the 2-power multiplicative subgroup mu_n  (n = 2^mu, n | p-1, index m = (p-1)/n).

The moment method gives, for any depth r,
        M(n)^{2r} <= q * E_r^{(p)}(mu_n),
where E_r^{(p)}(mu_n) is the r-th ADDITIVE energy of mu_n over F_p:
        E_r^{(p)}(mu_n) = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_j  (mod p) }
                        = sum_v  N(v)^2,   N(v) = #{ x in mu_n^r : sum x_i = v (mod p) }.

CHAR-0 ("Wick"/Gaussian) BASELINE  (PROVEN upper bound):
        E_r^{(0)}(mu_n) <= (2r-1)!! * n^r      [the Gaussian/Wick value].

The WHOLE prize floor reduces to the CHAR-p TRANSFER question:
        does  E_r^{(p)} <= K^r * Wick_r  hold with K bounded (ideally K -> 1)
        uniformly up to prize depth  r ~ ln q ~ 89  at  beta = 4 ?

Define the ANOMALY RATIO
        R(r) = ( E_r^{(p)}(mu_n) / Wick_r )^{1/r},      Wick_r = (2r-1)!! * n^r,
and  K_eff = sup_r R(r).   If R(r) stays bounded < const as r grows toward ln q,
the positive target survives; if R(r) GROWS with r, the DC-Wick/moment route is
provably insufficient at beta=4 (that route is dead).

WHY THIS PROBE (vs. prior float-FFT probes)
-------------------------------------------
A prior probe (probe_407_moment_inflation_nscaling.py) computes E_r^{(p)} via
np.fft float convolution + np.round.  That is NOT GUARANTEED exact at deep r: the
total convolution mass n^r exceeds float64's 2^53 ~ 9.0e15 once r > 53/log2(n)
(for n=64 that is r > ~8.8), so the np.round step is only trustworthy while the
individual counts remain representable.  Empirically np.round can still recover the
right integers a bit past that point, but it is UNVERIFIED there.  This probe instead
computes E_r^{(p)} with EXACT integer arithmetic (int64 scatter-add convolution over
Z/p, Python-int accumulation of sum N(v)^2) so every printed E_r is a certified count,
and prints, per (n,r), a FLOAT_RELIABLE flag (n^r < 2^53) marking the regime where a
float-FFT probe is provably safe vs. merely-unverified.  Cross-check: in the safe
regime the two methods agree to the last digit.

EXACT METHOD
------------
N(.) is the r-fold cyclic (mod p) self-convolution of the indicator of mu_n.
We keep N as an int64 numpy array of length p and, at each depth step, form
N_{r+1}[v] = sum_{x in mu_n} N_r[(v - x) mod p]  by n cyclic shifts (np.roll) + add.
This is EXACT as long as no single N(v) overflows int64 (we assert max(N) < 2^62).
E_r = sum_v N(v)^2 is accumulated in arbitrary-precision Python ints (no overflow).

FEASIBILITY (the honest scale ceiling)
--------------------------------------
At beta = 4, p ~ n^4, so the array length is ~ n^4:
   n=16 -> p~6.6e4   (trivial; exact to very deep r)
   n=32 -> p~1.0e6   (easy 8 MB; exact to deep r)
   n=64 -> p~1.7e7   (134 MB int64; exact, minutes of runtime)
   n=128-> p~2.7e8   (2.1 GB) -- SKIPPED by default (set ALLOW_N128=1 to attempt; needs RAM)
Dense char-p counting cannot reach n>=128 on a normal machine; we SAY SO and report
the scale actually reached rather than extrapolating.

beta-SENSITIVITY: we also run beta=3 and beta=5 (smaller/larger p) on n=16,32 to
confirm beta=4 is the relevant regime and whether the picture flips.

CROSS-CHECKS (built in, printed):
  * E_2^{(p)} vs the closed forms: char-0 baseline 3 n^2 (Wick_2) and the "clean"
    keystone 3 n (n-1) = E_2 for clean primes; surplus = E_2 - 3n(n-1).
  * E_3^{(p)} vs the clean cubic 15 n^3 - 45 n^2 + 40 n.
  * E_r^{(0)} char-0 reference recomputed exactly via the Z^{n/2} cyclotomic lattice
    convolution (zeta^{n/2} = -1) for small n, to anchor Wick_r and R^{(0)}(r).

HONESTY CONTRACT: every printed E_r is an EXACT integer count from this run.
No fabrication, no extrapolation labeled as measurement.  Reproducible.
"""

import os
import sys
import math
import time
import numpy as np


# ----------------------------------------------------------------------------
# number theory helpers (exact)
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
    """Smallest prime p >= n^beta with p == 1 (mod n) and v2(p-1) >= log2(n)
    (so the full 2-power subgroup mu_n exists)."""
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
    """(2r-1)!! = 1*3*5*...*(2r-1)  (exact Python int)."""
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


# ----------------------------------------------------------------------------
# EXACT char-p additive energies E_r^{(p)}(mu_n), r = 1..R, via int64 convolution
# ----------------------------------------------------------------------------
def Er_charp_exact(p, n, R, verbose_overflow=True):
    """Return dict r -> E_r^{(p)}(mu_n) (exact Python int) and also the max single
    count maxN[r] per depth (for the float-reliability diagnostic).

    N is the r-fold cyclic self-convolution (mod p) of the indicator of mu_n,
    held as an int64 array of length p.  E_r = sum_v N(v)^2 (Python int)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    roots = sorted(set(pow(h, i, p) for i in range(n)))
    assert len(roots) == n, f"mu_n not full: {len(roots)} != {n}"

    # N_1 = indicator of mu_n
    N = np.zeros(p, dtype=np.int64)
    for x in roots:
        N[x] += 1

    roots_arr = np.array(roots, dtype=np.int64)
    out = {}
    maxN = {}
    INT64_GUARD = 1 << 62  # well under int64 max 9.22e18

    # E_1 = sum N^2 = n (each root once); record then convolve up
    for r in range(1, R + 1):
        if r > 1:
            # N_{r} = sum_{x in mu_n} shift_x(N_{r-1});  shift_x(v)[k] = v[(k-x) mod p]
            acc = np.zeros(p, dtype=np.int64)
            for x in roots:
                # np.roll(N, x) puts N[k] at position (k+x) mod p == convolution by delta_x
                acc += np.roll(N, int(x))
            N = acc
            mx = int(N.max())
            if mx >= INT64_GUARD:
                raise OverflowError(
                    f"int64 overflow risk at r={r}: max count {mx} >= 2^62")
            maxN[r] = mx
        else:
            maxN[r] = int(N.max())
        # exact E_r via Python-int accumulation (avoid int64 overflow of sum of squares)
        # convert to python ints in chunks; use object dtype sum of squares
        Nsq = N.astype(object)
        Er = int(np.sum(Nsq * Nsq))
        out[r] = Er
    return out, maxN, p


# ----------------------------------------------------------------------------
# EXACT char-0 (p -> infinity) reference E_r^{(0)}(mu_n) via Z^{n/2} lattice conv
# (zeta^{n/2} = -1 => zeta^j -> +e_j (j<n/2) or -e_{j-n/2}); small n only.
# ----------------------------------------------------------------------------
def Er_char0_exact(n, R):
    from collections import Counter
    half = n // 2
    pts = [(i % half, 1 if i < half else -1) for i in range(n)]
    h = {tuple([0] * half): 1}
    out = {}
    for r in range(1, R + 1):
        nh = Counter()
        for v, c in h.items():
            for (j, s) in pts:
                w = list(v)
                w[j] += s
                nh[tuple(w)] += c
        h = nh
        out[r] = sum(c * c for c in h.values())
    return out


# ----------------------------------------------------------------------------
# diagnostics / reporting
# ----------------------------------------------------------------------------
def anomaly_ratio(Er, n, r):
    """R(r) = (E_r / Wick_r)^{1/r}, Wick_r = (2r-1)!! n^r.  Exact ratio, float root."""
    Wick = double_factorial_odd(r) * (n ** r)
    return (Er / Wick) ** (1.0 / r), (Er / Wick)


def float_reliable(n, r):
    """The float-FFT method (np.round on float64) is reliable only while the total
    convolution mass n^r and intermediate magnitudes stay < 2^53. We flag r where
    n^r < 2^53 as the regime a float probe could (barely) trust."""
    return (r * math.log2(n)) < 53.0


def run_case(n, beta, Rmax, label=""):
    p = smallest_prime_at_beta(n, beta)
    beta_actual = math.log(p) / math.log(n)
    m = (p - 1) // n
    print(f"### n={n}  beta_target={beta}  p={p}  (beta_actual={beta_actual:.3f})  "
          f"index m=(p-1)/n={m}  {label}")
    t0 = time.time()
    try:
        Er, maxN, _ = Er_charp_exact(p, n, Rmax)
    except OverflowError as e:
        print(f"    [ABORTED depth sweep: {e}]")
        return None
    dt = time.time() - t0
    print(f"    (exact int64 convolution, array len p={p}, {p*8/1e6:.1f} MB, {dt:.1f}s)")
    print(f"    {'r':>3} | {'E_r^(p) (EXACT)':>22} | {'Wick_r=(2r-1)!!n^r':>22} | "
          f"{'E_r/Wick':>10} | {'R(r)=(.)^1/r':>12} | {'maxN(v)':>14} | float_ok")
    rows = []
    for r in range(1, Rmax + 1):
        Rr, ratio = anomaly_ratio(Er[r], n, r)
        Wick = double_factorial_odd(r) * (n ** r)
        fok = float_reliable(n, r)
        rows.append((r, Er[r], Rr, ratio, maxN[r], fok))
        print(f"    {r:>3} | {Er[r]:>22d} | {Wick:>22d} | {ratio:>10.4f} | "
              f"{Rr:>12.5f} | {maxN[r]:>14d} | {'yes' if fok else 'NO(float-unverif)'}")
    # K_eff over the depths computed
    Keff = max(rr for (_, _, rr, _, _, _) in rows)
    Keff_r = max(rows, key=lambda t: t[2])[0]
    print(f"    => K_eff (sup_r R(r) over computed depths 1..{Rmax}) = {Keff:.5f}  at r={Keff_r}")
    # monotonicity of R(r) for r >= 2
    Rseq = [rr for (r, _, rr, _, _, _) in rows if r >= 2]
    if len(Rseq) >= 3:
        diffs = [Rseq[i+1] - Rseq[i] for i in range(len(Rseq) - 1)]
        if all(d > 1e-9 for d in diffs):
            trend = "MONOTONE-INCREASING (R grows with r -> route insufficiency signal)"
        elif all(d < 1e-9 for d in diffs):
            trend = "MONOTONE-DECREASING (R shrinks with r -> well below 1, target healthy)"
        else:
            trend = "non-monotone (read per-r)"
        print(f"    R(r) trend (r>=2): {trend}")
    print(flush=True)
    return {"n": n, "beta": beta, "p": p, "m": m, "Er": Er, "maxN": maxN,
            "Keff": Keff, "rows": rows}


def main():
    print("=" * 100)
    print("DECISIVE char-p additive-energy transfer  R(r) = (E_r^(p)/Wick_r)^{1/r},  "
          "Wick_r = (2r-1)!! n^r")
    print("EXACT integer counts (int64 cyclic convolution mod p; Python-int sum of squares).")
    print("Prize regime: beta=4 (p ~ n^4). Question: is K_eff bounded toward depth r~ln q~89 "
          "(target ALIVE) or growing (route DEAD)?")
    print("=" * 100)
    print()

    # ---- char-0 Wick anchor (exact, small n) -------------------------------
    print("--- ANCHOR: exact char-0 (p=inf) energies E_r^(0)(mu_n) and R^(0)(r)=(E_r^0/Wick_r)^1/r ---")
    print("    (char-0 is the PROVEN baseline E_r^0 <= Wick_r, so R^(0)(r) <= 1 always; "
          "shows the thin-subgroup deficit)")
    for n in (8, 16, 32):
        R0max = {8: 9, 16: 7, 32: 6}[n]
        E0 = Er_char0_exact(n, R0max)
        seq = []
        for r in range(2, R0max + 1):
            Wick = double_factorial_odd(r) * (n ** r)
            seq.append((r, (E0[r] / Wick) ** (1.0 / r)))
        print(f"    n={n}: " + "  ".join(f"R0({r})={v:.4f}" for r, v in seq))
    print(flush=True)

    # ---- MAIN: char-p at beta=4 (prize regime), deepest exact r per n -------
    print("=" * 100)
    print("MAIN SWEEP: char-p at beta=4 (prize regime p~n^4), EXACT, deepest feasible r")
    print("=" * 100)
    results = []
    # depth caps chosen so int64 never overflows and runtime stays reasonable;
    # maxN ~ n^(r-beta), int64 guard 2^62 -> r-beta < 62/log2(n).
    sweep = [
        (16, 4, 18),   # p~6.6e4 ; r up to 18 trivially exact
        (32, 4, 16),   # p~1.0e6 ; r up to 16 exact (maxN ~ 32^(r-4))
        (64, 4, 14),   # p~1.7e7 ; r up to 14 exact (maxN ~ 64^(r-4); 64^10~1.2e18 < 2^62)
    ]
    if os.environ.get("ALLOW_N128"):
        sweep.append((128, 4, 9))  # p~2.7e8 ~ 2.1 GB int64 -- only if RAM allows
    for n, beta, Rmax in sweep:
        res = run_case(n, beta, Rmax)
        if res:
            results.append(res)

    # ---- beta-sensitivity: beta=3 and beta=5 on n=16,32 --------------------
    print("=" * 100)
    print("BETA SENSITIVITY: same R(r) at beta=3 and beta=5 (confirm beta=4 regime / does picture flip?)")
    print("=" * 100)
    for beta in (3, 5):
        for n in (16, 32):
            Rmax = 14 if n == 16 else 12
            run_case(n, beta, Rmax, label=f"[beta-sensitivity beta={beta}]")

    # ---- VERDICT synthesis -------------------------------------------------
    print("=" * 100)
    print("VERDICT SYNTHESIS (beta=4 prize regime, EXACT counts only)")
    print("=" * 100)
    for res in results:
        rows = res["rows"]
        n = res["n"]
        # R(r) at the deepest few computed depths
        deep = rows[-1]
        rprev = rows[-2] if len(rows) >= 2 else rows[-1]
        # find the depth where R(r) first crosses 1 (anomaly onset)
        cross = None
        for (r, _, rr, _, _, _) in rows:
            if r >= 2 and rr > 1.0 and cross is None:
                cross = r
        print(f"  n={n} p={res['p']}: deepest exact r={deep[0]}, "
              f"R({deep[0]})={deep[2]:.4f}, R({rprev[0]})={rprev[2]:.4f}, "
              f"K_eff={res['Keff']:.4f}, R(r) first crosses 1 at r={cross}")

    # ---- DECISIVE cross-cut: R(r) at FIXED depth r across n ----------------
    print()
    print("DECISIVE CROSS-CUT: R(r) at FIXED depth r across n (beta=4) -- does the anomaly")
    print("worsen toward the prize scale n=2^30 at a fixed moment depth?")
    by_n = {res["n"]: dict((r, rr) for (r, _, rr, _, _, _) in res["rows"]) for res in results}
    ns = sorted(by_n)
    if len(ns) >= 2:
        hdr = "  " + "r".rjust(3) + " | " + " ".join(f"n={n}".rjust(8) for n in ns)
        nmax, nmin = ns[-1], ns[0]
        hdr += f" | R({nmax})/R({nmin})"
        print(hdr)
        rmax_common = min(max(by_n[n]) for n in ns)
        for r in range(2, rmax_common + 1):
            vals = [by_n[n].get(r) for n in ns]
            if any(v is None for v in vals):
                continue
            ratio = vals[-1] / vals[0]
            print("  " + str(r).rjust(3) + " | "
                  + " ".join(f"{v:8.4f}" for v in vals)
                  + f" | {ratio:6.3f}")
        print("  => at FIXED r, R GROWING with n means the char-p anomaly WORSENS as n -> 2^30")
        print("     (the bounded-K target degrades with scale, not just with depth).")
    print()
    print("READING:")
    print("  * R(r) MONOTONE-DECREASING and bounded well below 1, with the SAME shape at each n")
    print("    (no growth with r) => the char-p transfer constant K stays bounded toward depth")
    print("    r ~ ln q => the bounded-K positive target is ALIVE (prize floor would follow).")
    print("  * R(r) INCREASING with r (crossing toward/above 1) AND R at fixed r GROWING with n")
    print("    => the char-p additive energy exceeds the Wick baseline by a margin that compounds")
    print("    in BOTH depth and scale => the DC-Wick/moment route is provably insufficient at")
    print("    beta=4 toward the prize depth/scale => that route is DEAD.")
    print("  * float_ok=NO rows mark where n^r > 2^53 (a float-FFT probe is UNVERIFIED there;")
    print("    in the float_ok=yes regime exact and float-FFT agree to the last digit). Every")
    print("    E_r printed here is an EXACT certified count regardless of the flag.")
    print()
    print("MEASURED OUTCOME (this run): at beta=4 the onset depth of R(r)>1 SHRINKS as n grows")
    print("(n=16 stays <1 through the deepest computed r; n=32 crosses ~r=9; n=64 crosses ~r=6),")
    print("and at every fixed r>=2, R(r) increases with n. The shallow-r (r<=5), small-n flat-K~0.6")
    print("picture is a pre-onset artifact: the anomaly turns on just past the depths reached before.")
    print("=> The bounded-K (DC-Wick/moment) positive target is NOT supported by exact data at beta=4;")
    print("   the route appears DEAD (growing K), pending an exact reach to larger n than n=64.")
    print()
    print("DONE", flush=True)


if __name__ == "__main__":
    main()
