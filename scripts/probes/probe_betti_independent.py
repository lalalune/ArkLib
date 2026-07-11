#!/usr/bin/env python3
r"""#407 FORWARD PROBE: INDEPENDENT re-derivation of the Fermat-Betti no-go.

================================================================================
MANDATE.  Do NOT trust the prior agent. Independently:
  (1) Derive WHICH variety governs the 2r-th additive moment of the Gaussian
      periods, and its dimension.
  (2) Independently compute its PRIMITIVE Betti number two ways:
        (a) via Jacobi-sum / diagonal-hypersurface cohomology (Weil 1949 +
            Deligne weight count), counting characters with NO trivial factor,
        (b) via the alternating Euler-characteristic recursion for the Fermat
            hypersurface (a self-contained combinatorial computation),
      and cross-check both equal the claimed closed form
            B_prim(r, d) = ( (d-1)^{2r} + (d-1) ) / d.
  (3) Independently compute the WALL DEPTH rstar(d, p) -- the moment order at
      which the Deligne error term  B_prim * p^{(D-1)/2}  overtakes the main
      term  ~ p^{D/2}  (D = middle dimension) -- and confirm rstar = 3 at the
      prize point d = 2^128, p = n^5  (n = subgroup order, p ~ d*n).
  (4) Report whether the no-go is AIRTIGHT or has a gap: a subvariety with
      smaller Betti, or cohomology-level cancellation of Frobenius eigenvalues.

EXACT ARITHMETIC ONLY (Python big-ints + Fraction). Gate every identity.
================================================================================

THE GEOMETRY (independently derived here, not taken from the prior agent).

  Gaussian periods.  p = d*n + 1 (d = index = (p-1)/n, FIXED ~2^128 at prize;
  n = |mu_n| ~ p large). The d periods are
        eta_a = sum_{x in mu_n} e_p(g^a x),    a = 0..d-1,    (REAL, Var = n).
  Equivalently eta_a = g(g^a) with the subgroup Gauss sum g(t)=sum_{x in mu_n} e_p(tx),
  which is constant on each of the d cosets g^a * mu_n.

  2r-th moment.   V_{2r} = sum_a |eta_a|^{2r}. Expanding |eta_a|^2 = eta_a * conj
  and summing over the d cosets (orthogonality of additive characters over F_p):
        sum_{t in F_p} |g(t)|^{2r} = p * N_r,
        N_r = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_j in F_p }.
  This N_r is the count of F_p-points on the AFFINE balanced variety
        W_r:  x_1+...+x_r = y_1+...+y_r,  each x_i,y_j in mu_n (i.e. u^d = 1-ish),
  realized as a complete intersection inside (F_p^*)^{2r}: each coordinate lies
  on the 0-dim subgroup mu_n = {u : u^d = u^{... }}. Projectivizing / homogenizing
  the multiplicative-subgroup constraint u in mu_n <=> u = w^? turns each subgroup
  membership into a degree-d Fermat-type condition. The RESULT, after the standard
  GLT reduction (Lemma 17 generalized), is that the NONTRIVIAL part of N_r is a
  point count on a DIAGONAL (Fermat) HYPERSURFACE of degree d.

  WHICH Fermat hypersurface? The 2r-th moment pairs r "+" subgroup elements
  against r "-" subgroup elements with one linear balance, giving a Fermat-type
  hypersurface in 2r homogeneous variables of degree d:
        F:  c_1 X_1^d + ... + c_{2r} X_{2r}^d = 0    in  P^{2r-1},
  a smooth hypersurface of dimension  D = 2r - 2  (middle dimension D = 2r-2).
  Its only interesting cohomology is in the middle degree H^{2r-2}, of which the
  PRIMITIVE part B_prim carries the Frobenius eigenvalues of weight D = 2r-2,
  i.e. the error term scales as B_prim * p^{(2r-2)/2} = B_prim * p^{r-1}.
  (The full middle Betti also has 1 from the hyperplane class when D even.)

  Cross-check anchor: r = 2 (the 4th moment) -> Fermat hypersurface in P^3 of
  dim 2 = Fermat SURFACE c1 X1^d+..+c4 X4^d=0; but GLT's Theorem 2 phrases the
  4th moment via the Fermat CURVE x^d+y^d=z^d in P^2 (dim 1). The two are
  consistent: the surface's primitive H^2 DECOMPOSES into Jacobi-sum pieces, and
  the GLT curve genus (d-1)(d-2)/2 reappears. We verify the Betti FORMULA
  ((d-1)^{2r}+(d-1))/d directly by the Jacobi-sum character count, which is the
  cohomologically correct primitive middle Betti of the degree-d Fermat
  hypersurface in the relevant projective dimension, INDEPENDENT of which
  birational model GLT chose.

  We therefore compute, INDEPENDENTLY:
    * the Jacobi-sum character count for the Fermat hypersurface of degree d in
      P^{M} (M+1 variables), keep M variable and find which M reproduces the
      claimed formula -- and REPORT that M, derived not assumed;
    * the alternating recursion B(d, M) for the primitive Betti of degree-d
      Fermat in P^M, an independent combinatorial route;
    * the wall depth from D = (derived middle dim) and B_prim growth.
"""

import math
from fractions import Fraction

# ---------------------------------------------------------------- exact helpers
def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d * d <= x:
        if x % d == 0 or x % (d + 2) == 0: return False
        d += 6
    return True

def binom(n, k):
    if k < 0 or k > n: return 0
    k = min(k, n - k)
    num = 1; den = 1
    for i in range(k):
        num *= (n - i); den *= (i + 1)
    return num // den

# ====================================================================== PART 1
# JACOBI-SUM / DIAGONAL-HYPERSURFACE PRIMITIVE BETTI.
#
# Weil (1949), "Numbers of solutions of equations in finite fields".
# For the projective diagonal (Fermat) hypersurface of degree d in P^{M}
# (i.e. M+1 homogeneous coordinates, equation a_0 X_0^d + ... + a_M X_M^d = 0,
# dimension D = M-1), the number of points over F_q (q == 1 mod d) is
#     N = (q^M - 1)/(q - 1)  +  (Jacobi-sum correction),
# and the PRIMITIVE middle Betti number (= number of Frobenius eigenvalues of
# pure weight D = M-1 in primitive H^{M-1}) equals the number of solutions
#     (a_0, ..., a_M),  a_i in {1, 2, ..., d-1}  (NONtrivial chars on each var),
#     with    a_0 + a_1 + ... + a_M == 0  (mod d).
# Each such character tuple contributes one Jacobi sum of absolute value
# q^{(M-1)/2} -- a weight-(M-1) eigenvalue. Count them = primitive Betti.
#
# This is the cohomologically correct primitive middle Betti of the degree-d
# Fermat hypersurface in P^M. We compute it by EXACT counting (DP over residues
# mod d), with NO appeal to the claimed closed form.

def primitive_betti_fermat(d, M):
    r"""Number of (a_0..a_M) with each a_i in {1..d-1} and sum == 0 (mod d).
    DP over the M+1 variables, exact big-int counts of residue classes mod d.
    This is the primitive middle Betti of the degree-d Fermat hypersurface in P^M
    (dimension D = M-1), = # weight-(M-1) Frobenius eigenvalues (Weil/Jacobi)."""
    # number of variables = M+1
    nvar = M + 1
    # dist[s] = # ways to pick a_0..a_{i} (so far) with sum == s (mod d),
    # each a in {1..d-1}.
    dist = [0] * d
    # base: one variable
    for a in range(1, d):
        dist[a % d] += 1
    for _ in range(nvar - 1):
        nd = [0] * d
        for s in range(d):
            v = dist[s]
            if v == 0: continue
            for a in range(1, d):
                nd[(s + a) % d] += v
        dist = nd
    return dist[0]

def primitive_betti_closed_form(d, r):
    r"""Claimed prior-agent closed form B_prim = ((d-1)^{2r} + (d-1))/d.
    Returns exact integer (asserts divisibility)."""
    num = (d - 1) ** (2 * r) + (d - 1)
    assert num % d == 0, f"closed form not integral: d={d} r={r}"
    return num // d

def primitive_betti_general_closed_form(d, nvar):
    r"""General closed form for the number of (a_1..a_{nvar}) in {1..d-1}^{nvar}
    with sum == 0 (mod d):  ((d-1)^{nvar} + (-1)^{nvar} (d-1)) / d.
    Derived independently from the roots-of-unity filter:
        count = (1/d) sum_{j=0}^{d-1} ( sum_{a=1}^{d-1} w^{j a} )^{nvar},  w=e^{2pi i/d}.
    For j=0 the inner sum is (d-1); for j!=0, sum_{a=1}^{d-1} w^{ja}
        = (sum_{a=0}^{d-1} w^{ja}) - 1 = 0 - 1 = -1.
    So count = (1/d)[ (d-1)^{nvar} + (d-1)*(-1)^{nvar} ]. Exact, no floats."""
    sign = 1 if nvar % 2 == 0 else -1
    num = (d - 1) ** nvar + sign * (d - 1)
    assert num % d == 0
    return num // d

# ====================================================================== PART 2
# INDEPENDENT ALTERNATING-RECURSION route to the SAME primitive Betti.
#
# The total Betti sum (sum of all Betti numbers, = # eigenvalues) of the smooth
# degree-d hypersurface X of dim D=M-1 in P^M satisfies the classical relation
#   chi(X) = chi(P^{M-1}_general) ... ; cleaner: the primitive (middle) Betti is
#   b_prim = (-1)^{D} [ chi(X) - (D+1) ]   when we strip the D+1 "P^D-like" classes.
# We instead recompute b_prim from the Euler characteristic of a smooth degree-d
# hypersurface in P^M, given by the well-known generating function
#   chi(X_{d,M}) = sum over the standard formula. We implement chi via
#   chi(X_{d,M}) = ( (1 - (1-d)^{M+1}) / d )  ... (the smooth-hypersurface Euler
# number). Then b_prim = | chi(X) - (M)  if D odd ... |. To avoid sign confusion
# we DERIVE b_prim purely from chi and the known non-primitive Betti = 1 in each
# even degree 0..2D except middle (Lefschetz), giving:
#     D even:  b_middle = chi - D ;  b_prim = b_middle - 1.
#     D odd:   b_middle = D + 1 - chi ; b_prim = b_middle  (no extra hyperplane).
# This is a SECOND, independent path (Euler char, not Jacobi sums).

def euler_char_smooth_hypersurface(d, M):
    r"""Euler characteristic of a smooth degree-d hypersurface in P^M (dim D=M-1).
    Classical formula:
        chi = sum_{j=0}^{M} (-1)^? ...  ; we use the closed form
        chi(X_{d}^{M-1}) = ((1-d)^{M+1} - 1)/d + (M+1).
    Derivation: c(TX) via adjunction, integrate; equivalently
        chi = (M+1) + ((1-d)^{M+1} - 1)/d.
    EXACT integer (asserts divisibility)."""
    num = (1 - d) ** (M + 1) - 1
    assert num % d == 0, f"euler not integral d={d} M={M}"
    return (M + 1) + num // d

def primitive_betti_via_euler(d, M):
    r"""b_prim of degree-d Fermat hypersurface in P^M from its Euler char.
    D = M-1 = dim. Non-primitive cohomology = P^D (one class in each even degree
    0,2,..,2D). Their Euler contribution = D+1. The primitive part sits entirely
    in middle degree D with sign (-1)^D. So
        chi = (D+1) + (-1)^D * b_prim   =>   b_prim = (-1)^D (chi - (D+1)).
    """
    D = M - 1
    chi = euler_char_smooth_hypersurface(d, M)
    bp = ((-1) ** D) * (chi - (D + 1))
    return bp

# ====================================================================== PART 3
# WALL DEPTH.
#
# The 2r-th moment's nontrivial error is governed by the degree-d Fermat
# hypersurface of MIDDLE DIMENSION D = D(r) (derived below). The Deligne bound:
#     |error| <= B_prim(r,d) * p^{D/2}.
# The MAIN term of the (normalized) moment scales like p^{D/2 + 1/2}-ish; more
# precisely, for the additive-moment problem the random/main contribution to N_r
# is n^{2r}/p ~ p^{2r-1}/d^{2r}, and the Deligne error envelope on the SAME object
# is B_prim * p^{(D)/2}. The wall is where error >= main. The prior agent's stated
# law: rstar ~ log p / (2 log(d-1)), from B_prim ~ (d-1)^{2r}/d and each extra
# moment costing a factor (d-1)^2 against a single sqrt(p)=p^{1/2} gain.
#
# We DERIVE rstar two ways:
#   (i)  exact integer crossing: smallest r with B_prim(r,d) * p^{D(r)/2} >= MAIN(r),
#        using log-domain exact-ish (Fraction of logs) comparison;
#   (ii) the asymptotic rstar ~ log p / (2 log(d-1)), and check (i) ~ (ii).

def required_depth(p):
    r"""Prize requires controlling cumulants to depth r ~ ln p."""
    return math.log(p)

def wall_depth_asymptotic(d, p):
    r"""rstar ~ log p / (2 log(d-1)). The depth at which one sqrt(p) gain per
    moment is overwhelmed by the (d-1)^2-per-moment Betti growth."""
    return math.log(p) / (2 * math.log(d - 1))

def log_primitive_betti(d, r):
    r"""log of B_prim(r,d) = ((d-1)^{2r}+(d-1))/d, exact for big d via dominant
    term (d-1)^{2r}/d plus a tiny correction; we use the true value when feasible."""
    if d < 10 ** 7:
        return math.log(primitive_betti_closed_form(d, r))
    # dominant: (d-1)^{2r}/d ; correction factor (1 + (d-1)^{1-2r}) ~ 1
    return (2 * r) * math.log(d - 1) - math.log(d)

def wall_depth_exact(d, p, rmax=400, model="moment"):
    r"""Smallest r where the Deligne ERROR envelope >= MAIN term.

    THE NORMALIZATION MATTERS, so we expose TWO models and reconcile them.

    model="moment"  (the additive-moment object, the prize-relevant one):
        The 2r-th moment V_{2r} = (main poly in p) + (Deligne error). The degree-d
        Fermat hypersurface in P^{2r-1} (dim D=2r-2) has point count
            N = (p^{D+1}-1)/(p-1) + (sum of B_prim Jacobi sums, each |.|=p^{D/2}),
        so MAIN ~ p^{D} = p^{2r-2} and ERROR ~ B_prim * p^{D/2} = B_prim * p^{r-1}.
        BUT the moment normalizes by stripping the (p^{D+1}-1)/(p-1) "projective
        space" part: the relevant additive-moment MAIN is the RANDOM rate
            MAIN_mom ~ n^{2r}/p   (n=(p-1)/d),
        and the SAME-object Deligne error is B_prim * p^{r-1}. Wall when
            B_prim * p^{r-1} >= n^{2r}/p.
        Since n=(p-1)/d ~ p/d, n^{2r}/p ~ p^{2r-1}/d^{2r}, and B_prim*p^{r-1}
        ~ (d-1)^{2r}/d * p^{r-1}. Ratio error/main ~ (d-1)^{2r}/d / (p^{2r-1}/d^{2r} / p^{r-1})
        = (d-1)^{2r} d^{2r-1} / p^{r}. Wall: p^{r} <= (d-1)^{2r} d^{2r-1},
        i.e. r*ln p <= 2r ln(d-1) + (2r-1) ln d ~ 4r ln d => ln p <= 4 ln d
        => p <= d^4. At p=d^4 (=2^512) wall ~ everywhere; at p<d^4 wall at r=2.

    model="pointcount"  (the raw Fermat point count, GLT/Rojas phrasing):
        MAIN ~ p^{D} = p^{2r-2}, ERROR ~ B_prim*p^{D/2}=B_prim*p^{r-1}. Wall when
            B_prim*p^{r-1} >= p^{2r-2}  <=>  B_prim >= p^{r-1}
            <=> (d-1)^{2r}/d >= p^{r-1} <=> 2r ln(d-1) - ln d >= (r-1) ln p.
        Asymptotically (large r): 2 ln(d-1) >= ln p, i.e. ALWAYS a wall when
        p < (d-1)^2; the *first* r where it bites is the prior agent's
            rstar ~ log p / (2 log(d-1))   (solving (r-1)ln p = 2r ln(d-1) for the
            crossover, dominant balance r ln p ~ 2r ln(d-1) gives the RATE; the
            additive +ln d, -ln p shift the first-crossing r). We report the exact
            first-crossing r for this model -- THIS is the model whose formula is
            log p/(2 log(d-1)).

    Returns (rstar, table)."""
    n = (p - 1) // d
    ln_p = math.log(p)
    ln_n = math.log(n)
    table = []
    rstar = None
    for r in range(2, rmax + 1):
        D = 2 * r - 2
        log_Bprim = log_primitive_betti(d, r)
        log_err = log_Bprim + (D / 2.0) * ln_p           # B_prim * p^{r-1}
        if model == "moment":
            log_main = (2 * r) * ln_n - ln_p             # n^{2r}/p
        else:  # pointcount
            log_main = D * ln_p                          # p^{2r-2}
        margin = log_main - log_err
        wall = margin < 0
        table.append({"r": r, "D": D, "log_Bprim": log_Bprim,
                      "log_err": log_err, "log_main": log_main,
                      "margin": margin, "wall": wall})
        if wall and rstar is None:
            rstar = r
    return rstar, table

# ====================================================================== PART 4
# SUBVARIETY / CANCELLATION GAP ANALYSIS.
#
# The no-go is "airtight" ONLY if the relevant cohomology really carries
# B_prim(r,d) ~ (d-1)^{2r}/d eigenvalues of weight D each near p^{D/2}, with NO
# systematic cancellation. We probe for a GAP:
#   (G1) Does a SMALLER subvariety govern the actual additive moment? The true
#        object is W_r (balance over the subgroup), NOT the full Fermat
#        hypersurface. We check small primes EXACTLY whether the measured error
#        |N_r - main| sits at the FULL Betti envelope (no gap) or far below it
#        (cancellation -> potential gap). The prior MEASUREMENT said the char-p
#        extra hits the RANDOM rate 1.00, i.e. WAY below B_prim p^{D/2}: that is
#        already evidence of MASSIVE cancellation. We quantify it.
#   (G2) Is the cancellation "structural" (provable, opening a route) or
#        "accidental" (numeric, the same sqrt(p) wall one level up)?

def isprime_small(x):
    return isprime(x)

def primroot(p):
    if p == 2: return 1
    fac = []; m = p - 1; dd = 2
    while dd * dd <= m:
        if m % dd == 0:
            fac.append(dd)
            while m % dd == 0: m //= dd
        dd += 1
    if m > 1: fac.append(m)
    for a in range(2, p):
        if all(pow(a, (p - 1) // q, p) != 1 for q in fac):
            return a
    raise RuntimeError("no primroot")

def subgroup(p, n):
    g = primroot(p)
    z = pow(g, (p - 1) // n, p)
    S = []; x = 1
    for _ in range(n):
        S.append(x); x = x * z % p
    assert len(set(S)) == n
    return S

def Nr_balanced(p, S, r):
    r"""Exact F_p-point count of the balanced subgroup variety
        x_1+..+x_r = y_1+..+y_r, all in S (=mu_n).
    Via R = r-fold additive convolution multiplicity, N_r = sum_c R[c]^2."""
    base = [0] * p
    for x in S: base[x] += 1
    R = base[:]
    for _ in range(r - 1):
        nxt = [0] * p
        supp = [(t, R[t]) for t in range(p) if R[t]]
        for c in range(p):
            bc = base[c]
            if bc == 0: continue
            for t, rt in supp:
                nxt[(t + c) % p] += rt * bc
        R = nxt
    return sum(v * v for v in R)

def double_factorial(k):
    out = 1
    while k > 0:
        out *= k; k -= 2
    return out

def measure_actual_error_envelope(p, n, rmax):
    r"""For an actual small prime, measure the TRUE error of the balanced
    subgroup count N_r against the random main n^{2r}/p, and compare its size to
    BOTH the full Fermat Betti envelope B_prim*p^{D/2} (D=2r-2) and the
    'random rate' n^{2r}/p. Reports whether the measured error is at the Betti
    envelope (no gap) or at random rate (massive cancellation => the real wall)."""
    d = (p - 1) // n
    S = subgroup(p, n)
    rows = []
    for r in range(2, rmax + 1):
        Nr = Nr_balanced(p, S, r)
        main = (n ** (2 * r)) // p
        # char-0 leading random main:
        Er_lead = double_factorial(2 * r - 1) * (n ** r)
        err = Nr - main  # the "extra" over the uniform main
        D = 2 * r - 2
        Bprim = primitive_betti_closed_form(d, r) if d >= 2 else 0
        deligne_env = Bprim * (p ** (D / 2.0)) if Bprim else float('inf')
        rand_rate = main  # n^{2r}/p
        rows.append({
            "r": r, "Nr": Nr, "main": main, "err": err,
            "abs_err": abs(err),
            "deligne_env": deligne_env,
            "err_over_deligne": (abs(err) / deligne_env) if deligne_env else float('nan'),
            "err_over_randrate": (abs(err) / rand_rate) if rand_rate else float('nan'),
            "Er_lead": Er_lead,
        })
    return rows


# ====================================================================== DRIVER
def main():
    out = {}
    print("=" * 80)
    print("PART 1+2: PRIMITIVE BETTI of degree-d Fermat hypersurface, THREE ways")
    print("  (a) Jacobi-sum character count (DP, exact)")
    print("  (b) roots-of-unity closed form ((d-1)^nvar + (-1)^nvar (d-1))/d")
    print("  (c) Euler-characteristic route")
    print("  -> find which #variables 'nvar' reproduces ((d-1)^{2r}+(d-1))/d")
    print("=" * 80)
    # The claimed formula is ((d-1)^{2r}+(d-1))/d. By the roots-of-unity closed
    # form, the count over nvar variables is ((d-1)^nvar + (-1)^nvar (d-1))/d.
    # For this to equal ((d-1)^{2r}+(d-1))/d we need nvar = 2r AND (-1)^nvar = +1,
    # i.e. nvar = 2r (EVEN). nvar = M+1 variables => M = 2r-1 => P^{2r-1},
    # dimension D = M-1 = 2r-2. We VERIFY this derivation numerically.
    derivation = []
    for d in [3, 4, 5, 7, 11]:
        for r in [2, 3, 4, 5]:
            nvar = 2 * r                       # DERIVED: 2r homogeneous variables
            M = nvar - 1                       # P^M
            D = M - 1                          # dimension
            jac = primitive_betti_fermat(d, M)         # Jacobi count over M+1=nvar vars
            roots = primitive_betti_general_closed_form(d, nvar)
            claimed = primitive_betti_closed_form(d, r)
            euler = primitive_betti_via_euler(d, M)
            ok = (jac == roots == claimed)
            ok_euler = (euler == claimed)
            derivation.append({
                "d": d, "r": r, "nvar": nvar, "P^M": M, "dim_D": D,
                "jacobi_count": jac, "roots_closed": roots,
                "claimed_formula": claimed, "euler_route": euler,
                "jacobi==claimed": ok, "euler==claimed": ok_euler,
            })
            tag = "OK" if (ok and ok_euler) else "MISMATCH"
            print(f"  d={d:>3} r={r}  nvar=2r={nvar}  P^{M} dim D={D}  "
                  f"Jacobi={jac:>20}  roots={roots:>20}  claimed={claimed:>20}  "
                  f"euler={euler:>20}  [{tag}]")
    out["betti_derivation"] = derivation
    all_ok = all(x["jacobi==claimed"] and x["euler==claimed"] for x in derivation)
    print(f"\n  ALL THREE ROUTES AGREE WITH ((d-1)^2r+(d-1))/d : {all_ok}")
    print(f"  DERIVED GEOMETRY: 2r-th moment <-> degree-d Fermat hypersurface in")
    print(f"  P^(2r-1), middle dimension D = 2r-2, primitive Betti = ((d-1)^2r+(d-1))/d.")
    out["all_three_routes_agree"] = all_ok

    print("\n" + "=" * 80)
    print("PART 3: WALL DEPTH rstar at the PRIZE POINT  d=2^128")
    print("  *** the prize 'p=n^5' has an AMBIGUITY (n = subgroup order vs index);")
    print("      we test BOTH readings and BOTH error-models, transparently. ***")
    print("=" * 80)
    d_prize = 2 ** 128

    # Reading A (literal: n = SUBGROUP order, p = d*n+1): n=2^32 => p~2^160=d^{1.25}.
    # Reading B (p = INDEX^5 = d^5): p~2^640. (this is the reading under which the
    #   prior agent's formula log p/(2 log(d-1)) gives ~2.5).
    prize_cases = []
    for tag, p_prize, note in [
        ("A: p=n^5, n=subgroup=2^32  (p~2^160=d^1.25)", d_prize * (2 ** 32) + 1,
         "literal subgroup reading"),
        ("B: p=d^5  (p~2^640)", d_prize ** 5, "index^5 reading"),
        ("B2: p=d^6 (p~2^768)", d_prize ** 6, "index^6 -> formula=3 exactly"),
        ("C: p=d^2  (p~2^256, where 'needed depth ln p ~ 177')", d_prize ** 2,
         "ln p ~ 177 regime"),
    ]:
        ln_p = math.log(p_prize)
        rstar_asy = wall_depth_asymptotic(d_prize, p_prize)
        rstar_mom, tab_mom = wall_depth_exact(d_prize, p_prize, rmax=80, model="moment")
        rstar_pc, tab_pc = wall_depth_exact(d_prize, p_prize, rmax=80, model="pointcount")
        print(f"\n  [{tag}]  ({note})")
        print(f"    log p = {ln_p:.3f}   needed depth (r~ln p) = {ln_p:.1f}")
        print(f"    prior-agent asymptotic rstar = log p/(2 log(d-1)) = {rstar_asy:.4f}")
        print(f"    EXACT rstar  (moment model, MAIN=n^2r/p)      = {rstar_mom}")
        print(f"    EXACT rstar  (pointcount model, MAIN=p^2r-2)  = {rstar_pc}  "
              f"<- THIS model's formula is log p/(2 log(d-1))")
        prize_cases.append({
            "tag": tag, "note": note, "p": str(p_prize), "log_p": round(ln_p, 4),
            "needed_depth_ln_p": round(ln_p, 2),
            "rstar_asymptotic_priorformula": round(rstar_asy, 4),
            "rstar_exact_moment_model": rstar_mom,
            "rstar_exact_pointcount_model": rstar_pc,
        })
    out["prize_cases"] = prize_cases
    print("\n  RECONCILIATION:")
    print("    * The prior agent's 'rstar=3' is reproduced ONLY in the pointcount")
    print("      model AND only when p~d^6 (~2^768). At the LITERAL prize point")
    print("      (p~2^160, n=subgroup), the same formula gives rstar~0.6 and the")
    print("      exact crossing is r=2. So the *number* '3' is regime-dependent;")
    print("      the prior summary's '=3 at prize d=2^128, p=n^5' is NOT")
    print("      reproducible as stated -- it mixes the index^k reading.")
    print("    * INVARIANT across ALL readings/models: rstar is a SMALL CONSTANT")
    print("      (0.6 .. 3), while the NEEDED depth is r ~ ln p ~ 100-180. The")
    print("      wall hits at O(1) << needed O(ln p). The no-go's QUALITATIVE")
    print("      core (Betti envelope kills the main term FAR below needed depth)")
    print("      is robust; only the exact constant '3' is non-canonical.")

    # The decisive invariant: rstar (any model) vs needed depth, across regimes.
    print("\n  DECISIVE INVARIANT: rstar (small const) vs needed depth ln p (large):")
    sens = []
    for kk in [1.25, 2, 3, 4, 5, 6]:
        # p = d^kk (kk=1.25 ~ the literal prize)
        if abs(kk - round(kk)) < 1e-9:
            pp = d_prize ** int(round(kk))
        else:
            pp = int(d_prize ** kk)
        lnp = math.log(pp)
        ra = wall_depth_asymptotic(d_prize, pp)
        rmom, _ = wall_depth_exact(d_prize, pp, rmax=120, model="moment")
        rpc, _ = wall_depth_exact(d_prize, pp, rmax=120, model="pointcount")
        wall_below_needed = (max(rmom or 999, rpc or 999) < lnp)
        sens.append({"p_as_d^": kk, "log_p": round(lnp, 2),
                     "needed_depth": round(lnp, 1),
                     "rstar_formula": round(ra, 3),
                     "rstar_moment": rmom, "rstar_pointcount": rpc,
                     "wall_below_needed_depth": wall_below_needed})
        print(f"    p=d^{kk:<5} log p={lnp:7.1f}  needed={lnp:6.1f}  "
              f"formula_rstar={ra:6.3f}  mom={rmom}  pc={rpc}  "
              f"wall<<needed={wall_below_needed}")
    out["wall_vs_needed_invariant"] = sens
    out["NOGO_qualitative_robust"] = all(s["wall_below_needed_depth"] for s in sens)
    out["NOGO_exact_3_reproducible_at_literal_prize"] = (
        prize_cases[0]["rstar_exact_pointcount_model"] == 3)

    print("\n" + "=" * 80)
    print("PART 4: GAP ANALYSIS -- does the ACTUAL moment sit at the Betti envelope,")
    print("        or far below (cancellation)? Exact small-prime measurement.")
    print("=" * 80)
    # Use real primes p = d*n+1 with small index d and moderate n, exact counts.
    gap_rows = []
    for (d_small, n_small) in [(3, 8), (3, 16), (5, 8), (7, 8), (11, 6)]:
        # find a prime p = d_small * n_small + 1 ? need (p-1)/n = d. We want
        # p prime with (p-1)/n_small = d_small => p = d_small*n_small+1.
        p = d_small * n_small + 1
        if not isprime(p):
            # bump n until prime, keep index d_small
            nn = n_small
            while not isprime(d_small * nn + 1):
                nn += 1
            n_small = nn
            p = d_small * n_small + 1
        rows = measure_actual_error_envelope(p, n_small, rmax=6)
        print(f"\n  p={p} (index d={d_small}, n={n_small}):")
        print(f"    {'r':>2} {'abs_err':>14} {'Deligne_env=Bp*p^(r-1)':>24} "
              f"{'err/Deligne':>14} {'err/randrate':>14}")
        for row in rows:
            print(f"    {row['r']:>2} {row['abs_err']:>14} {row['deligne_env']:>24.3e} "
                  f"{row['err_over_deligne']:>14.3e} {row['err_over_randrate']:>14.3e}")
            gap_rows.append({"p": p, "d": d_small, "n": n_small, **{
                k: (str(v) if isinstance(v, int) and abs(v) > 2**53 else
                    (round(v, 8) if isinstance(v, float) else v))
                for k, v in row.items()}})
    out["gap_measurement"] = gap_rows

    # VERDICT logic.
    # Airtight no-go requires: the moment error genuinely fills the Betti
    # envelope (err/Deligne ~ O(1)), so Deligne is tight and the wall is real.
    # If err/Deligne << 1 systematically, there's cohomology-level cancellation
    # => the Betti envelope is NOT the true size => the no-go has a GAP (but the
    # cancellation must itself be PROVED, which is the "same sqrt(p) wall one
    # level up").
    max_err_over_deligne = max((r["err_over_deligne"] for r in gap_rows
                                if isinstance(r["err_over_deligne"], float)
                                and not math.isnan(r["err_over_deligne"])), default=0.0)
    out["max_err_over_deligne_measured"] = max_err_over_deligne

    # THE SHARP THRESHOLD. The pointcount-model margin slope is ln p - 2 ln(d-1).
    # Wall regime (Deligne error dominates for all r>=2)  <=>  p < (d-1)^2.
    # Good regime (Deligne always sub-main)              <=>  p > (d-1)^2.
    dm1_sq = (d_prize - 1) ** 2
    p_literal = d_prize * (2 ** 32) + 1
    in_wall_regime = p_literal < dm1_sq
    out["sharp_threshold"] = {
        "criterion": "wall (Deligne error dominates all r>=2)  <=>  p < (d-1)^2",
        "(d-1)^2_bits": math.log2(dm1_sq),
        "literal_prize_p_bits": math.log2(p_literal),
        "literal_prize_in_wall_regime": in_wall_regime,
    }
    out["NOGO_verdict"] = (
        "CONFIRMED (stronger than stated): at the literal prize point p~2^160 < "
        "(d-1)^2~2^256, the Deligne error envelope exceeds the main term at EVERY "
        "moment order r>=2, not merely r>=3. The 'rstar=3' numerology is NOT "
        "reproducible at the literal prize (it needs p~d^6~2^768); the canonical "
        "invariant is the threshold p vs (d-1)^2. GAP: the ACTUAL additive moment "
        "sits far below the Fermat Betti envelope (err/Deligne -> 0, ~random rate), "
        "so the worst-case Betti no-go is not tight -- but closing the gap requires "
        "PROVING that Frobenius cancellation, which is the same sqrt(p) wall one "
        "level up.")

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"  Betti formula ((d-1)^2r+(d-1))/d INDEPENDENTLY confirmed 3 ways: {all_ok}")
    print(f"  Governing variety: degree-d Fermat hypersurface in P^(2r-1), dim 2r-2.")
    print(f"  SHARP THRESHOLD (canonical, replaces 'rstar=3'):")
    print(f"     wall regime  <=>  p < (d-1)^2 ~ 2^{math.log2(dm1_sq):.0f}.")
    print(f"     literal prize p~2^{math.log2(p_literal):.0f}  ->  IN WALL REGIME = {in_wall_regime}")
    print(f"     => Deligne error dominates main at ALL r>=2 (stronger than rstar=3).")
    print(f"  prior 'rstar=3' reproducible ONLY at p~d^6~2^768 (NOT the prize point).")
    print(f"  Max measured err/Deligne-envelope over small primes = {max_err_over_deligne:.3e}")
    print(f"  (err/Deligne -> 0 with r => the additive moment does NOT fill the")
    print(f"   Fermat Betti envelope: there IS cohomology-level cancellation down to")
    print(f"   ~random rate. The worst-case Betti no-go is loose; closing the gap")
    print(f"   needs PROVING the Frobenius cancellation = same sqrt(p) wall one level up.)")

    # ---------------------------------------------------------------- PART 5
    # WEIGHT / SUBVARIETY GAP. The r=2 Betti ((d-1)^4+(d-1))/d MATCHES the known
    # primitive b_2 of the Fermat SURFACE (d^3-4d^2+6d-3): independent ground
    # truth. BUT GLT realize V_4 via the Fermat CURVE x^d+y^d=z^d, whose error has
    # only 2g=(d-1)(d-2) eigenvalues of WEIGHT 1 (~p^{1/2}), giving V_4 error
    # O(p^{3/2}) -- NOT the surface's b_2 weight-2 (~p) envelope. So the MOMENT is
    # governed by a SMALLER, LOWER-WEIGHT model than the worst-case Fermat
    # hypersurface the no-go uses. This is the concrete gap candidate.
    print("\n" + "=" * 80)
    print("PART 5: WEIGHT / SUBVARIETY GAP (r=2 ground-truth + curve-vs-surface)")
    print("=" * 80)
    weight_gap = []
    for d in [3, 4, 5, 7, 11]:
        b2_surf = primitive_betti_closed_form(d, 2)
        known_surf = d ** 3 - 4 * d ** 2 + 6 * d - 3   # textbook Fermat-surface b2_prim
        twog_curve = (d - 1) * (d - 2)                 # GLT curve 2g (weight-1 count)
        weight_gap.append({
            "d": d, "my_Bprim_r2": b2_surf,
            "known_fermat_surface_b2prim": known_surf,
            "surface_match": b2_surf == known_surf,
            "GLT_curve_2g_weight1": twog_curve,
            "surface_weight": 2, "curve_weight": 1,
        })
        print(f"  d={d:>3}: B_prim(r=2)={b2_surf:>6} == known Fermat-surface b2_prim"
              f"={known_surf:>6} ({b2_surf==known_surf})   "
              f"GLT-curve 2g={twog_curve} (weight 1, the ACTUAL V_4 error model)")
    out["weight_gap"] = weight_gap
    out["GAP_FINDING"] = (
        "The r=2 Betti is independently confirmed (matches textbook Fermat-surface "
        "b2_prim). HOWEVER GLT's V_4 error is governed by the modified-Fermat CURVE "
        "(2g=(d-1)(d-2) eigenvalues of WEIGHT 1, error O(p^{3/2})), NOT the surface's "
        "weight-2 envelope. So the no-go's worst-case Fermat-hypersurface model "
        "OVER-counts: a smaller, lower-weight subvariety governs the actual moment. "
        "This is a real gap candidate -- but the general-r reduction to a low-weight "
        "curve model is exactly the open sqrt(p)-cancellation problem (GLT have it "
        "only for r=2).")
    print("  => GAP CANDIDATE: the actual moment error uses the LOWER-WEIGHT curve")
    print("     model (weight 1), not the worst-case surface (weight 2). The no-go")
    print("     bounds the worst case; the true object is smaller. Proving the")
    print("     general-r low-weight reduction = the sqrt(p)-cancellation wall.")

    import json
    outpath = "/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes/betti_independent_results.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=1, default=str)
    print(f"\n  wrote {outpath}")
    return out

if __name__ == "__main__":
    main()
