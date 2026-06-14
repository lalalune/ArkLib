#!/usr/bin/env python3
"""
probe_gp_relation_threshold.py  --  PIN the relation-threshold formula r*(n,beta).

CONTEXT (Proximity Prize, Conjecture (G), the ONE open link).
  mu_n = subgroup of n-th roots of unity in F_p* (n=2^mu | p-1, n < p-1 PROPER).
  S_b = sum_{x in mu_n} e_p(b x); the m=(p-1)/n Gaussian periods eta_i are the distinct
  REAL values of S_b over the m cosets.  Var(eta_i)=n, E_2=3n^2-3n (kurtosis 3).
  The moment method controls max_i|eta_i| via the EXACT additive moment
      E_r(mu_n) = #{(x_1..x_r,y_1..y_r) in mu_n^{2r} : sum x_i = sum y_j (mod p)}
                = (1/p) sum_b |S_b|^{2r}.
  Char-0 Gaussian value is E_r^0 = (2r-1)!! n^r.  Conjecture (G) needs the F_p moment to
  stay <= E_r^0 (sub-Gaussian) up to depth r ~ log m.  The "relation threshold"
      r*(n,beta) := smallest r with  E_r^{F_p} / [(2r-1)!! n^r] > 1
  marks where F_p-genuine additive relations start to dominate and the Gaussian count is
  exceeded.  The moment proof of (G) goes through iff r*(n,beta) exceeds the optimal moment
  depth (~ (1/2) log m, see below).

WHAT THIS PROBE DOES (the assigned ANGLE).
  For a grid n in {8,16,32,64} and beta in {3,3.5,4,4.5,5,5.5}, pick several primes p ~ n^beta
  (p == 1 mod n), compute E_r EXACTLY (integer convolution over Z_p) to a depth deep enough to
  capture the UPTURN of the ratio curve, and record:
      r*1 = first r with ratio > 1     (the relation threshold for (G) as stated)
      r*2 = first r with ratio > 2     (a robust "genuine relations dominate" mark)
      rmin = argmin of the ratio curve, ratio_min = the minimum value (slack at best depth)
  Then tabulate r*1(n,beta), fit candidate laws  r* ~ (beta-1) log_2 n,  ~ beta,  ~ c beta log n,
  and compare r* to the optimal moment depth and to log m, producing the (n,beta)-plane boundary
  separating "(G)'s moment proof goes through" from "moments cross too early".

OPTIMAL MOMENT DEPTH.  The moment bound is  max_i|eta_i| <= (p/n * E_r)^{1/2r}  (since
sum_i eta_i^{2r} = (1/n) sum_{b!=0}|S_b|^{2r} <= (1/n)(p E_r) and max <= (sum)^{1/2r}).
Plugging E_r = (2r-1)!! n^r ~ (2r/e)^r n^r gives a bound that is minimized over r; the optimal r
for the standard sub-Gaussian-from-moments argument with m periods is r_opt ~ (1/2) log m (this is
the r that balances the (m)^{1/2r} prefactor against the moment growth, giving the sqrt(2 n log m)
floor).  So the moment proof of (G) is VALID at a given (n,beta) iff  r*1(n,beta) >= r_opt ~ (1/2) log m.
We report BOTH the r >= log m criterion (conservative, as literally stated) and the
r >= (1/2) log m criterion (the actual optimal-moment-depth criterion).

EXACTNESS / HONESTY.
  E_r is the TRUE integer additive-relation count, computed by r-fold convolution of the indicator
  of mu_n over Z_p in EXACT integer arithmetic (int64 while n^r < 2^60, else Python big-int via
  object dtype).  No floating point enters the moment.  float (numpy) is used ONLY for the
  independent variance gate sum_i|eta_i|^2 = p-n.  Correctness gates E_1=n, E_2=3n^2-3n,
  Var=p-n are asserted; any (p,n) failing a gate is dropped from the verdict.
"""

import numpy as np
import math
import json
import sys
import time


# ---------------------------------------------------------------------------
# number theory helpers (self-contained; no sympy)
# ---------------------------------------------------------------------------

def is_prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    if x % 3 == 0:
        return x == 3
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a % x == 0:
            continue
        v = pow(a, d, x)
        if v == 1 or v == x - 1:
            continue
        ok = False
        for _ in range(s - 1):
            v = (v * v) % x
            if v == x - 1:
                ok = True
                break
        if not ok:
            return False
    return True


def prime_factors(m):
    f = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            f.add(d)
            m //= d
        d += 1
    if m > 1:
        f.add(m)
    return f


def order_n_element(p, n):
    assert (p - 1) % n == 0
    pf = prime_factors(n)
    for g in range(2, p):
        z = pow(g, (p - 1) // n, p)
        if all(pow(z, n // q, p) != 1 for q in pf):
            return z
    raise RuntimeError("no order-n element")


def subgroup(p, n):
    z = order_n_element(p, n)
    return sorted(pow(z, j, p) for j in range(n))


def primes_near(n, target, count):
    """primes p == 1 (mod n), p >= target, the first `count` of them."""
    out = []
    start = target + ((1 - (target % n)) % n)
    if start < target:
        start += n
    p = start
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def dbl_fact_odd(twoR_minus_1):
    k = twoR_minus_1
    r = 1
    j = 1
    while j <= k:
        r *= j
        j += 2
    return r


# ---------------------------------------------------------------------------
# EXACT integer additive moments E_r via r-fold convolution over Z_p
# ---------------------------------------------------------------------------

def exact_moments(p, G, rmax):
    """
    dict r -> E_r (exact int) for r = 1..rmax.
      A_1 = indicator of G;  A_{r+1}(t) = sum_{a in G} A_r((t-a) mod p);  E_r = sum_t A_r(t)^2.
    int64 while n^r < 2^60, else object (Python big-int).  Exact throughout.
    """
    n = len(G)
    res = {}

    use_object_from = rmax + 1
    for r in range(2, rmax + 1):
        if r * math.log2(n) >= 60.0:
            use_object_from = r
            break

    A = np.zeros(p, dtype=np.int64)
    for x in G:
        A[x] = 1
    res[1] = int(np.dot(A, A))  # = n, exact (small)

    promoted = False
    for r in range(2, rmax + 1):
        if (not promoted) and r >= use_object_from:
            A = A.astype(object)
            promoted = True
        newA = np.zeros(p, dtype=(object if promoted else np.int64))
        for a in G:
            newA += np.roll(A, int(a))
        A = newA
        if promoted:
            # object dtype: np.dot is exact (Python big-int multiply/add) and ~5x faster
            # than a Python loop; verified equal to the loop on random data.
            Er = int(np.dot(A, A))
        else:
            # int64 squares can overflow; sum via python ints from .tolist()
            Er = 0
            for v in A.tolist():
                Er += v * v
        res[r] = int(Er)
    return res


def variance_gate(p, G):
    ind = np.zeros(p)
    for x in G:
        ind[x] = 1.0
    F = np.fft.fft(ind)
    sb2 = np.abs(F) ** 2
    n = len(G)
    sum_nonzero = float(sb2[1:].sum())
    per_period_sum = sum_nonzero / n
    maxabs = float(np.abs(F[1:]).max())
    return per_period_sum, p - n, maxabs


# ---------------------------------------------------------------------------
# main sweep
# ---------------------------------------------------------------------------

def analyze_curve(E, n, rmax):
    """Return r*1 (first ratio>1), r*2 (first ratio>2), rmin (argmin), ratio_min, ratios dict."""
    ratios = {}
    for r in range(2, rmax + 1):
        denom = dbl_fact_odd(2 * r - 1) * (n ** r)
        ratios[r] = E[r] / denom
    rstar1 = next((r for r in range(2, rmax + 1) if ratios[r] > 1.0), None)
    rstar2 = next((r for r in range(2, rmax + 1) if ratios[r] > 2.0), None)
    rmin = min(ratios, key=lambda r: ratios[r])
    return rstar1, rstar2, rmin, ratios[rmin], ratios


def run():
    print("=" * 100)
    print("RELATION-THRESHOLD r*(n,beta)  --  exact deep-moment sweep")
    print("r*1 = first r with E_r/[(2r-1)!! n^r] > 1   (the Conjecture-(G) relation threshold)")
    print("Compared to r_opt ~ (1/2) log m (optimal moment depth) and to log m (conservative).")
    print("=" * 100)

    grid_n = [8, 16, 32, 64]
    grid_beta = [3.0, 3.5, 4.0, 4.5, 5.0, 5.5]
    primes_per_cell = 4

    # depth cap per n: must be large enough to pass the upturn at small beta,
    # but object-dtype cost ~ O(rmax * n * p). Keep p modest by capping target.
    # We cap p so the run finishes; for large (n,beta) p would be huge so we cap
    # the prime target and note beta_eff (actual beta of the chosen prime).
    P_CAP = 6_000_000  # keep convolutions fast; p above this is skipped with a note
    RMAX = {8: 24, 16: 22, 32: 20, 64: 18}

    records = []
    table = {}  # (n, beta_label) -> list of r*1
    t0 = time.time()

    for n in grid_n:
        print(f"\n{'#'*92}\n# n = {n}   (rmax={RMAX[n]})\n{'#'*92}")
        for beta in grid_beta:
            target = int(round(n ** beta))
            if target > P_CAP:
                print(f"  [beta={beta}] target p~{target} > P_CAP={P_CAP}: skipped (convolution too large)")
                continue
            ps = primes_near(n, target, primes_per_cell)
            if ps and ps[0] > P_CAP:
                print(f"  [beta={beta}] nearest prime {ps[0]} > P_CAP: skipped")
                continue
            ps = [p for p in ps if p <= P_CAP]
            cell_key = (n, beta)
            table[cell_key] = []
            for p in ps:
                G = subgroup(p, n)
                m = (p - 1) // n
                if m <= n:  # would be improper / degenerate; skip
                    continue
                beta_eff = math.log(p) / math.log(n)
                logm = math.log(m)
                rmax = min(RMAX[n], max(8, int(math.ceil(logm)) + 6))
                E = exact_moments(p, G, rmax)

                gate_E1 = (E[1] == n)
                gate_E2 = (E[2] == 3 * n * n - 3 * n)
                ppsum, pn, maxabs = variance_gate(p, G)
                gate_var = abs(ppsum - pn) < 1e-6 * max(1, pn)
                gates_ok = gate_E1 and gate_E2 and gate_var

                rstar1, rstar2, rmin, ratio_min, ratios = analyze_curve(E, n, rmax)

                r_opt = 0.5 * logm           # optimal moment depth
                conservative = logm          # literal "r ~ log m" statement
                # criterion: moment proof goes through iff first crossing > optimal depth
                proof_ok_opt = (rstar1 is None) or (rstar1 > r_opt)
                proof_ok_cons = (rstar1 is None) or (rstar1 > conservative)
                # did we cap before crossing? (rstar1 None but ratio still rising)
                capped_before_cross = (rstar1 is None and ratios[rmax] > ratios[rmin] * 1.05
                                       and rmax < RMAX[n])

                rec = {
                    "n": n, "p": p, "beta_target": beta, "beta_eff": round(beta_eff, 4),
                    "m": m, "logm": round(logm, 4), "rmax": rmax,
                    "rstar1": rstar1, "rstar2": rstar2, "rmin": rmin,
                    "ratio_min": round(ratio_min, 5),
                    "ratio_at_rmax": round(ratios[rmax], 5),
                    "r_opt": round(r_opt, 3), "log2n": round(math.log2(n), 3),
                    "maxabs": round(maxabs, 4),
                    "sqrt2nlogm": round(math.sqrt(2 * n * logm), 4),
                    "gates_ok": gates_ok,
                    "proof_ok_opt": proof_ok_opt, "proof_ok_cons": proof_ok_cons,
                    "capped_before_cross": capped_before_cross,
                    "ratios": {str(r): round(ratios[r], 5) for r in ratios},
                }
                records.append(rec)
                if gates_ok and rstar1 is not None:
                    table[cell_key].append(rstar1)

                gate_str = "OK" if gates_ok else f"FAIL(E1={gate_E1},E2={gate_E2},var={gate_var})"
                cs = "none" if rstar1 is None else str(rstar1)
                note = " [CAPPED before cross]" if capped_before_cross else ""
                print(f"  beta_eff={beta_eff:.3f} p={p} logm={logm:.2f} r_opt={r_opt:.2f} "
                      f"| rmin={rmin}(ratio={ratio_min:.3f}) r*1={cs} r*2={rstar2} "
                      f"| max|eta|={maxabs:.1f}/{math.sqrt(2*n*logm):.1f} gates={gate_str}{note}")

    print(f"\n[elapsed {time.time()-t0:.1f}s]")

    # ---------------------------------------------------------------------
    # TABLE r*1(n,beta)  (median over primes per cell)
    # ---------------------------------------------------------------------
    print("\n" + "=" * 100)
    print("TABLE  r*1(n,beta)  (median first-crossing over primes in cell; '-' = never crossed in range)")
    print("=" * 100)
    header = "  n\\beta " + "".join(f"{b:>7.1f}" for b in grid_beta)
    print(header)
    fit_rows = []  # (n, beta, rstar_median, logm_median, log2n)
    for n in grid_n:
        row = f"  {n:>5} "
        for beta in grid_beta:
            vals = table.get((n, beta), [])
            if vals:
                med = sorted(vals)[len(vals)//2]
                row += f"{med:>7}"
                # find a representative logm for this cell
                lm = None
                for rec in records:
                    if rec["n"] == n and rec["beta_target"] == beta and rec["gates_ok"]:
                        lm = rec["logm"]
                        break
                fit_rows.append((n, beta, med, lm, math.log2(n)))
            else:
                # check if cell was skipped vs never-crossed
                skipped = not any(rec["n"] == n and rec["beta_target"] == beta for rec in records)
                row += "   skip" if skipped else "      -"
        print(row)

    # ---------------------------------------------------------------------
    # FITS:  r*1 ~ a*(beta-1)*log2(n) + b ;  r*1 ~ c*beta + d ;  r*1 ~ e*beta*log2(n)+f
    # ---------------------------------------------------------------------
    print("\n" + "=" * 100)
    print("FITS for r*1(n,beta)  (least squares over all crossed cells)")
    print("=" * 100)
    if len(fit_rows) >= 3:
        ys = np.array([fr[2] for fr in fit_rows], dtype=float)
        betas = np.array([fr[1] for fr in fit_rows], dtype=float)
        l2n = np.array([fr[4] for fr in fit_rows], dtype=float)

        def lsq(X, name, terms):
            coef, res, rank, sv = np.linalg.lstsq(X, ys, rcond=None)
            pred = X @ coef
            ss_res = float(np.sum((ys - pred) ** 2))
            ss_tot = float(np.sum((ys - ys.mean()) ** 2))
            r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
            rmse = math.sqrt(ss_res / len(ys))
            print(f"  {name}")
            for t, c in zip(terms, coef):
                print(f"        {t:>16} : {c:+.4f}")
            print(f"        R^2 = {r2:.4f}   RMSE = {rmse:.3f}")
            return r2, rmse, coef

        X1 = np.column_stack([(betas - 1) * l2n, np.ones_like(ys)])
        lsq(X1, "MODEL A:  r* = a*(beta-1)*log2(n) + b", ["a*(beta-1)log2 n", "b (intercept)"])
        X2 = np.column_stack([betas, np.ones_like(ys)])
        lsq(X2, "MODEL B:  r* = c*beta + d", ["c*beta", "d (intercept)"])
        X3 = np.column_stack([betas * l2n, np.ones_like(ys)])
        lsq(X3, "MODEL C:  r* = e*beta*log2(n) + f", ["e*beta log2 n", "f (intercept)"])
        X4 = np.column_stack([l2n, betas, np.ones_like(ys)])
        lsq(X4, "MODEL D:  r* = g*log2(n) + h*beta + k", ["g*log2 n", "h*beta", "k (intercept)"])
        # the memory-conjectured law:  r* >= (beta-1) log2 n  -- test as a LOWER bound
        conj = (betas - 1) * l2n
        viol = int(np.sum(ys < conj - 1e-9))
        print(f"\n  CONJECTURED LOWER BOUND  r* >= (beta-1)*log2(n):")
        print(f"        cells where r*1 < (beta-1)log2 n : {viol} / {len(ys)}"
              f"   (min slack r*1-(beta-1)log2n = {float(np.min(ys-conj)):+.3f})")

    # ---------------------------------------------------------------------
    # BOUNDARY in (n,beta): where does moment proof of (G) go through?
    # ---------------------------------------------------------------------
    print("\n" + "=" * 100)
    print("MOMENT-PROOF BOUNDARY:  proof of (G) valid at (n,beta)  iff  r*1 > optimal depth (1/2 log m)")
    print("(also reporting the conservative criterion r*1 > log m)")
    print("=" * 100)
    print(f"  {'n':>4} {'beta':>6} {'logm':>7} {'(1/2)logm':>10} {'r*1':>5}  proof@opt  proof@cons")
    for rec in sorted(records, key=lambda r: (r["n"], r["beta_eff"])):
        if not rec["gates_ok"]:
            continue
        cs = "-" if rec["rstar1"] is None else str(rec["rstar1"])
        po = "YES" if rec["proof_ok_opt"] else "no"
        pc = "YES" if rec["proof_ok_cons"] else "no"
        cap = " (capped)" if rec["capped_before_cross"] else ""
        print(f"  {rec['n']:>4} {rec['beta_eff']:>6.2f} {rec['logm']:>7.2f} "
              f"{0.5*rec['logm']:>10.2f} {cs:>5}  {po:>8}  {pc:>9}{cap}")

    out = {
        "grid_n": grid_n, "grid_beta": grid_beta,
        "table_rstar1_median": {f"{k[0]}_{k[1]}": (sorted(v)[len(v)//2] if v else None)
                                for k, v in table.items()},
        "records": records,
    }
    here = __file__.rsplit("/", 1)[0]
    with open(here + "/gp_relation_threshold_results.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("\nresults -> scripts/probes/gp_relation_threshold_results.json")


if __name__ == "__main__":
    run()
    sys.exit(0)
