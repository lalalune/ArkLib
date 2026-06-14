#!/usr/bin/env python3
r"""#407 — THE DECISIVE BETTI COMPUTATION for the Garcia-Lorenz-Todd + Deligne route.

PRIZE (#407).  mu_n = dyadic subgroup of order n = 2^mu in F_p^*, index d = m = (p-1)/n
FIXED (~2^128) as p -> infty.  Want the floor  M(mu_n) = max_{b!=0} |eta_b| <= sqrt(2 n log m).
The eta_i (i = 0..d-1) are the d Gaussian periods, real, with variance n and the exact gate
    sum_i |eta_i|^2 = p - n   (Parseval / second moment, ALWAYS exact).

ESTABLISHED (char-0 side, rigorous, NOT redone here): the char-0 additive 2r-th moment
    E_r(mu_n) = #{(a_i,b_i) in mu_n^{2r}: sum a_i = sum b_i over Z[zeta_n]}  <=  (2r-1)!! n^r.
THE ONLY OPEN PART is the CHAR-P TRANSFER: the extra mod-p solutions
    extra_r = E_r^{F_p} - E_r^{char0}
            = #{(a_i,b_i) in mu_n^{2r}: sum a_i = sum b_i (mod p), but NOT over Z[zeta_n]}.
Measured extra_r / (n^{2r}/p) -> 1.00 (random-like) at prize primes.  To get the floor we need
    extra_r <= (n^{2r}/p)(1 + o(1))   to depth r ~ ln p,   i.e. kappa_r <= 1.

GLT (arXiv:2112.13886, Ramanujan J. 2025) PROVE this for r = 2 ONLY (the FOURTH moment V_4):
  - Thm 3 (d=3): 27 V_4(p) = 10 p^2 + 4(4 - M_3) p + 1, M_3 = #proj pts on x^3+y^3=z^3 / F_p,
                 and |27 V_4(p) - (6 p^2 + 12 p + 1)| <= 8 p^{3/2}.   <-- a CURVE, genus 1.
  - Thm 6 (d=4): V_4 via M_{4,1}, M_{4,2} on x^4+y^4=z^4 (genus 3) -> 6 sqrt(p) Hasse-Weil error.
  - Lemma 24:  M_{i,j,k} = d^2 c_{i,j,k} + d(delta..),  c_{i,j,k} = #{a,b in Gamma: a+g^j b=g^k},
               Gamma = <g^d> the subgroup of order k=n.  Genus of g^i x^d+g^j y^d=g^k z^d is
               (d-1)(d-2)/2, so Hasse-Weil error = 2 g sqrt(p) = (d-1)(d-2) sqrt(p).
GLT do NOT construct the V_6, V_8, ..., V_{2r} varieties.  THIS PROBE constructs them and tests
the Deligne (Weil II) verdict for the GENERAL 2r-th moment, which is what closing #407 requires.

----------------------------------------------------------------------------------------------
THE VARIETY GOVERNING THE 2r-TH MOMENT (the extension of GLT's curve correspondence).

Expand each |eta_s|^{2r} and sum over s by orthogonality of supercharacters.  Exactly as in
GLT Lemma 24 (the r=2 case), the additive 2r-th moment is a Z-linear combination (coeffs = O(d),
the delta-corrections) of solution counts
    c(j_1,...,j_{2r-1}) = #{(a_1,...,a_{2r}) in Gamma^{2r}:  a_1 + g^{j_1} a_2 + ... = 0},
and EACH such count is, by the standard substitution a_i = x_i^d  (Gamma = d-th powers = {x^d}),
the number of F_p-points of a DIAGONAL (modified Fermat) HYPERSURFACE
    g^{e_0} x_0^d + g^{e_1} x_1^d + ... + g^{e_{2r-1}} x_{2r-1}^d = 0           (*)
in P^{2r-1} over F_p.   (r=2 -> 3 vars after using homogeneity -> the CURVE in P^2.  In general
2r monomials, one projective relation: the hypersurface (*) has AMBIENT P^{2r-1}, so it is a
variety of DIMENSION 2r-2.)   [This is precisely the diagonal hypersurface family for which Weil
1949 computed the zeta function via Jacobi sums, and whose Betti numbers were given by Dolbeault.]

DELIGNE / WEIL II (the error term).  For the smooth diagonal hypersurface (*) of degree d in
P^{2r-1} (dimension D := 2r-2), the point count is
    #X(F_p) = (p^{D+1}-1)/(p-1)  +  (primitive middle cohomology Frobenius trace),
and |trace| <= B_prim(r,d) * p^{D/2}  =  B_prim(r,d) * p^{r-1},   where B_prim(r,d) is the
dimension of the primitive part of H^D_{et} = the relevant DELIGNE CONDUCTOR / Betti number.
The TOTAL sum-of-Betti conductor (Adolphson-Sperber / Katz style envelope) is B_tot(r,d).

THE EXACT FERMAT BETTI NUMBER (Dolbeault / Weil).  For the smooth degree-d hypersurface of
dimension D in P^{D+1}, the primitive middle Betti number is
    B_prim(D, d) = ((d-1)^{D+2} + (-1)^{D+2}(d-1)) / d .
(This is the number of "a in (Z/d)^{D+2} with all a_i != 0 and sum a_i = 0 mod d" = the number
of nonzero Jacobi-sum terms = b_prim of the Fermat hypersurface.  Equivalently the count of
characters contributing a sqrt-power Frobenius eigenvalue.)  For D = 2r-2, ambient P^{2r-1}:
    B_prim(r,d) = ((d-1)^{2r} + (d-1)) / d              (2r even -> (-1)^{2r}=+1).

----------------------------------------------------------------------------------------------
THE VERDICT TEST.  Random rate means extra_r ~ n^{2r}/p ~ (main term)/p.  The Deligne error of
the moment is (conductor) * p^{r-1}, and the moment lives at scale ~ n^{2r} ~ p^{2r} (n ~ p at
fixed index).  For the FLOOR we need, at depth r ~ ln p:
    Deligne error  <=  main term   <=>   B(r,d) * p^{r-1}  <=  C * (2r-1)!! n^r * p .
We compute B_prim(r,d) AND B_tot(r,d) exactly for r=2..20 and d = index (incl. prize d~2^128),
fit the growth in r, and decide:
  - "closes"      if B(r,d) grows sub-exponentially / stays below the error-budget ratio to r~ln p;
  - "confirms_wall" if B(r,d) ~ (d-1)^{2r}/d grows EXPONENTIALLY in r (rate (d-1)^2 per step),
    which at fixed d >> 1 instantly dominates any (2r-1)!! n^r p budget.
"""

from math import comb, log, lgamma, isqrt
import json


# ---------------------------------------------------------------------------
# 1.  Exact Betti numbers of the diagonal (Fermat) hypersurface.
# ---------------------------------------------------------------------------

def betti_prim_fermat(D, d):
    r"""Primitive middle Betti number of a smooth degree-d hypersurface of DIMENSION D
    in P^{D+1}:   ((d-1)^{D+2} + (-1)^{D+2}(d-1)) / d.   Exact integer (Dolbeault/Weil)."""
    num = (d - 1) ** (D + 2) + ((-1) ** (D + 2)) * (d - 1)
    assert num % d == 0, (D, d, num)
    return num // d


def betti_total_fermat(D, d):
    r"""Sum of ALL l-adic Betti numbers of the smooth degree-d hypersurface of dimension D in
    P^{D+1} (this is the Deligne 'sum of Betti numbers' conductor that bounds the FULL error,
    including lower-weight terms).  b_i = 1 for each even i != D in [0,2D], plus the middle
    b_D = (the non-primitive 1 if D even) + B_prim.  So:
        b_total = (#even i in [0,2D], i != D)            # the projective-space part
                + (1 if D even else 0)                   # the hyperplane class in the middle
                + B_prim(D,d).
    """
    # number of even integers i with 0 <= i <= 2D, i != D
    even_count = (2 * D) // 2 + 1  # = D+1 even integers in [0,2D]
    if D % 2 == 0:
        proj_part = even_count - 1  # remove the middle even index D, count it separately
        middle_extra = 1
    else:
        proj_part = even_count  # D odd, so D is not even; all even indices are off-middle
        middle_extra = 0
    return proj_part + middle_extra + betti_prim_fermat(D, d)


def moment_variety_dim(r):
    """The 2r-th moment hypersurface (*) sits in P^{2r-1}; its dimension is D = 2r-2."""
    return 2 * r - 2


# ---------------------------------------------------------------------------
# 2.  The char-0 main term and the random-rate budget.
# ---------------------------------------------------------------------------

def double_factorial_odd(twoR_minus_1):
    """(2r-1)!! = product of odd numbers up to 2r-1."""
    res = 1
    k = twoR_minus_1
    while k > 1:
        res *= k
        k -= 2
    return res


def log_main_term(r, n, p):
    """log of the char-0 main term contribution to the moment scale ~ (2r-1)!! n^r,
    times the random-rate denominator p (the budget the error must beat)."""
    # use log for huge numbers
    df = double_factorial_odd(2 * r - 1)
    return log(df) + r * log(n) + log(p)


# ---------------------------------------------------------------------------
# 3.  Sweep r = 2..20 over prize-shaped (n, d, p), compute B and the verdict ratio.
# ---------------------------------------------------------------------------

def find_prime_geq(x):
    """smallest prime >= x (for moderate x)."""
    def is_p(m):
        if m < 2:
            return False
        if m % 2 == 0:
            return m == 2
        i = 3
        while i * i <= m:
            if m % i == 0:
                return False
            i += 2
        return True
    m = int(x)
    if m % 2 == 0:
        m += 1
    while not is_p(m):
        m += 2
    return m


def sweep(d, n, p, r_max=20):
    """For fixed index d, subgroup order n, prime p (p-1 = d*n approx), report per r:
    Betti (prim & total), Deligne error exponent, main-term exponent, and verdict ratio."""
    rows = []
    for r in range(2, r_max + 1):
        D = moment_variety_dim(r)          # 2r-2
        Bp = betti_prim_fermat(D, d)
        Bt = betti_total_fermat(D, d)
        # Deligne error of the moment: B * p^{D/2} = B * p^{r-1}
        log_err_prim = log(Bp) + (r - 1) * log(p)
        log_err_tot = log(Bt) + (r - 1) * log(p)
        log_main = log_main_term(r, n, p)
        # verdict ratio: error / main  (need <= 1 for the floor)
        log_ratio_prim = log_err_prim - log_main
        log_ratio_tot = log_err_tot - log_main
        rows.append({
            "r": r, "D": D,
            "log_Bprim": log(Bp), "log_Btot": log(Bt),
            "log_err_prim": log_err_prim, "log_main": log_main,
            "log_ratio_prim": log_ratio_prim, "log_ratio_tot": log_ratio_tot,
        })
    return rows


def betti_growth_rate(d):
    r"""The per-r exponential growth rate of B_prim(r,d): B(r+1)/B(r) -> (d-1)^2.
    Returns log of that asymptotic ratio."""
    return 2.0 * log(d - 1)


# ---------------------------------------------------------------------------
# 4.  Direct exact small-d verification of the Betti formula against known Fermat data.
# ---------------------------------------------------------------------------

def verify_known_fermat():
    """Cross-check B_prim against textbook values:
       - d=3, D=1 (cubic CURVE x^3+y^3=z^3): genus 1 => B_prim (= b_1) should be 2.
       - d=4, D=1 (quartic curve): genus 3 => b_1 = 2g = 6.
       - d=3, D=2 (cubic SURFACE): b_prim of H^2 = 7 (27 lines, h^{2}=7 primitive),
         actually b_2(cubic surface)=7, b_prim=6.  Check formula gives the diagonal count.
       - d=5, D=3 (quintic 3-fold): b_3 = 204 (classic).
    """
    checks = []
    # curve genus g: b_1 = 2g, and genus of plane degree-d curve = (d-1)(d-2)/2
    for d in (3, 4, 5, 6):
        g = (d - 1) * (d - 2) // 2
        bp_formula = betti_prim_fermat(1, d)   # D=1
        checks.append(("curve b1=2g", d, 2 * g, bp_formula, 2 * g == bp_formula))
    # quintic threefold D=3, d=5: b_3 = 204
    checks.append(("quintic 3fold b3", 5, 204, betti_prim_fermat(3, 5),
                   betti_prim_fermat(3, 5) == 204))
    # cubic surface D=2, d=3: primitive b_2 = 6 (b_2 = 7 total minus 1 hyperplane)
    checks.append(("cubic surface b2_prim", 3, 6, betti_prim_fermat(2, 3),
                   betti_prim_fermat(2, 3) == 6))
    # cubic threefold D=3, d=3: b_3 = 10
    checks.append(("cubic 3fold b3", 3, 10, betti_prim_fermat(3, 3),
                   betti_prim_fermat(3, 3) == 10))
    return checks


# ---------------------------------------------------------------------------
# 5.  GLT r=2 exact gate: reproduce their fourth-moment Hasse-Weil error from our Betti.
# ---------------------------------------------------------------------------

def glt_r2_gate():
    """For r=2 the variety is the CURVE (D=1, ambient P^3 -> but GLT reduce to plane curve in
    P^2 by homogeneity, D=1, degree d).  Hasse-Weil error = 2g sqrt(p) = (d-1)(d-2) sqrt(p).
    Our B_prim(D=1,d) = 2g, and the moment-error exponent at r=2 is B * p^{D/2} = 2g * sqrt(p)
    -- MATCHING GLT Thm 3 (d=3: 2g=2, error 8 p^{3/2} is the SUMMED-over-d-curves count, but
    the per-curve Hasse-Weil is exactly 2 sqrt p = (d-1)(d-2) sqrt p with d=3)."""
    out = []
    for d in (3, 4, 5):
        g = (d - 1) * (d - 2) // 2
        out.append({"d": d, "genus": g, "Bprim_D1": betti_prim_fermat(1, d),
                    "hasse_weil_coeff_sqrtp": (d - 1) * (d - 2),
                    "matches_2g": betti_prim_fermat(1, d) == 2 * g})
    return out


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    print("=" * 90)
    print("#407 FERMAT-BETTI DECISIVE PROBE — does GLT+Deligne close the char-p side?")
    print("=" * 90)

    print("\n[0] Sanity: exact Betti formula vs known Fermat varieties")
    for name, d, expected, got, ok in verify_known_fermat():
        print(f"    {name:24s} d={d}: expected {expected:6d}  formula {got:6d}  {'OK' if ok else 'MISMATCH'}")

    print("\n[1] GLT r=2 gate (our Betti must reproduce their Hasse-Weil 2g sqrt(p)):")
    for row in glt_r2_gate():
        print(f"    d={row['d']}: genus={row['genus']}  B_prim(D=1)={row['Bprim_D1']}  "
              f"HW coeff={row['hasse_weil_coeff_sqrtp']} sqrt(p)  matches 2g: {row['matches_2g']}")

    # ---- Betti growth in r, at several fixed indices d ----
    print("\n[2] B_prim(r,d) growth in r (the DECISIVE quantity), per fixed index d:")
    print("    B_prim(r,d) = ((d-1)^{2r} + (d-1)) / d.  Ratio B(r+1)/B(r) -> (d-1)^2.")
    for d in (3, 4, 16, 128):
        seq = [betti_prim_fermat(2 * r - 2, d) for r in range(2, 9)]
        ratios = [seq[i + 1] / seq[i] for i in range(len(seq) - 1)]
        print(f"    d={d:4d}: B_prim(r=2..8) = {seq}")
        print(f"            ratios = {[round(x,3) for x in ratios]}  -> (d-1)^2 = {(d-1)**2}")

    # ---- The verdict sweep at prize-shaped parameters ----
    print("\n[3] VERDICT SWEEP — log(Deligne error / main term) over r, at prize-shaped (n,d,p).")
    print("    Floor needs ratio <= 1 (i.e. log_ratio <= 0) for ALL r up to ~ln p.")

    results = {"betti_checks": [[c[0], c[1], c[2], c[3], c[4]] for c in verify_known_fermat()],
               "glt_r2_gate": glt_r2_gate(),
               "sweeps": []}

    # prize-shaped: n ~ p (fixed index d), p = d*n + 1 ideally.  Use moderate d to keep
    # exact integers printable, AND the literal prize d = 2^128 to read off the asymptotic.
    configs = []
    # (a) small explicit indices with p computed so p-1 = d*n, p prime
    for (d, n) in [(3, 2**20), (4, 2**20), (16, 2**24), (128, 2**24)]:
        p = find_prime_geq(d * n + 1)
        configs.append((d, n, p))
    # (b) the literal prize point (index 2^128, n ~ p ~ 2^256); use logs only
    configs.append((2**128, 2**255, 2**256 + 1))  # p symbolic-scale; only logs used

    for (d, n, p) in configs:
        rows = sweep(d, n, p, r_max=20)
        # ln p (the depth we must reach)
        ln_p = log(p)
        depth = int(ln_p)
        print(f"\n    --- index d={d}  n={n}  p~2^{round(log(p,2),1)}  (need r up to ~ln p = {depth}) ---")
        print(f"        {'r':>3} {'D':>4} {'logBprim':>10} {'log_err':>10} {'log_main':>10} "
              f"{'log(err/main)':>14}  verdict")
        wall_hit_at = None
        for row in rows:
            lr = row["log_ratio_prim"]
            verdict = "OK(<=main)" if lr <= 0 else "ERROR>MAIN"
            if lr > 0 and wall_hit_at is None:
                wall_hit_at = row["r"]
            # print a sampling to keep output readable
            if row["r"] <= 8 or row["r"] == 20 or (wall_hit_at and row["r"] <= wall_hit_at + 1):
                print(f"        {row['r']:>3} {row['D']:>4} {row['log_Bprim']:>10.3f} "
                      f"{row['log_err_prim']:>10.3f} {row['log_main']:>10.3f} "
                      f"{lr:>14.3f}  {verdict}")
        msg = (f"        => Deligne error exceeds main term starting at r = {wall_hit_at}"
               if wall_hit_at else "        => error stays below main term through r=20")
        if wall_hit_at and wall_hit_at <= depth:
            msg += f"  (WALL: this is <= required depth ln p = {depth})"
        elif wall_hit_at:
            msg += f"  (beyond required depth ln p = {depth} -- would be OK if it held)"
        print(msg)
        results["sweeps"].append({
            "d": d, "n": n, "p": p, "ln_p": ln_p, "required_depth": depth,
            "betti_growth_log_rate_per_r": betti_growth_rate(d),
            "wall_hit_at_r": wall_hit_at,
            "wall_within_required_depth": bool(wall_hit_at and wall_hit_at <= depth),
            "rows": rows,
        })

    # ---- The clean asymptotic statement ----
    print("\n[4] CLEAN ASYMPTOTIC VERDICT")
    print("    Error/main ratio in logs: log B_prim + (r-1) log p - [ log((2r-1)!!) + r log n + log p ]")
    print("    With n ~ p (fixed index): r log n + log p ~ (r+1) log p; (r-1) log p on the error side.")
    print("    => log(err/main) ~ log B_prim - 2 log p - log((2r-1)!!)")
    print("       and log B_prim ~ 2r log(d-1).  So:")
    print("       log(err/main) ~ 2r log(d-1) - 2 log p - log((2r-1)!!).")
    print("    The 2r log(d-1) term GROWS LINEARLY IN r WITH SLOPE 2 log(d-1).")
    print("    At fixed prize index d = 2^128: slope = 2*128*log 2 ~ 177.4 per unit r.")
    print("    (2r-1)!! grows like (2r/e)^r ~ r log r -- POLYNOMIALLY weaker than the 2r log(d-1).")
    print("    => for ANY fixed d >= 3 the Betti error term BEATS the main term once")
    print(f"       2r log(d-1) > 2 log p + log((2r-1)!!), i.e. at r* ~ (log p)/log(d-1) << ln p.")
    print("    The required depth is r ~ ln p; the Betti wall arrives at r* ~ (ln p)/log(d-1),")
    print("    which for d>=3 is a CONSTANT FACTOR below -- but the error already EXCEEDS the")
    print("    main term there, so the Deligne envelope is USELESS well before depth ln p.")

    print("\n[5] THE PRIZE-POINT KNIFE-EDGE (exact coincidence).")
    print("    At the prize point d ~ 2^128, n ~ p (fixed index), the two per-r slopes COINCIDE:")
    print("      log(error) per r:  2 log(d-1) + log p   (Betti factor (d-1)^2, plus one p)")
    print("      log(main)  per r:  log(2r) + log n  ~  log(2r) + log p")
    print("    => net per-r drift of log(error/main) = 2 log(d-1) - log(2r).")
    for d in (2**128,):
        slope = 2.0 * log(d - 1)
        print(f"      2 log(d-1) = {slope:.2f};  log(2r) at r=10 ~ {log(20):.2f}.")
        print(f"      net drift per r ~ {slope:.1f} - {log(20):.1f} = +{slope-log(20):.1f}  (STRICTLY POSITIVE, HUGE).")
    print("    The (2r-1)!! 'enhancement' of the char-0 main term only contributes log(2r)~O(log r)")
    print("    per step -- it can NEVER offset the 2 log(d-1) ~ log p per-step Betti blow-up.")
    print("    VERDICT: confirms_wall.  B_prim(r,d) ~ (d-1)^{2r}/d is EXPONENTIAL in r with rate")
    print("    (d-1)^2; at any fixed index d>=3 (a fortiori d~2^128) the Deligne/Weil-II envelope")
    print("    exceeds the main term at r* = O(log p / log(d-1)) = O(1) for prize d, FAR below the")
    print("    required depth r ~ ln p.  GLT's curve method (r=2, genus (d-1)(d-2)/2, one sqrt(p))")
    print("    is the LAST controllable level; the variety dimension grows (D=2r-2) and the Betti")
    print("    conductor outruns the gain.  This is the SAME effective-conductor wall as Rojas-Leon")
    print("    thread (A): the sqrt(q) gain needs q large vs the conductor, but here conductor ~")
    print("    (d-1)^{2r} forces 'q large' = p > (d-1)^{2r}, i.e. r < log p/(2 log(d-1)) = O(1).")

    with open("/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes/fermat_betti_results.json", "w") as f:
        json.dump(results, f, indent=1, default=str)
    print("\n[written] scripts/probes/fermat_betti_results.json")


if __name__ == "__main__":
    main()
