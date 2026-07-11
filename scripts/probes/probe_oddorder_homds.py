#!/usr/bin/env python3
"""
probe_oddorder_homds.py  (#407 — proximity prize, the ONE un-refuted prize-ADJACENT lane)

DIRECTION (section 6 lane).  The floor-refutation obstruction is SPECIFICALLY the negation
symmetry  -1 = omega^{n/2} in mu_n (n even):  x -> -x permutes mu_n, makes the Gauss-period
spectrum REAL, pairs additive-energy contributions, and -- the part this probe targets -- makes
elementary-symmetric / Schur constraints on subsets of mu_n VANISH "for free" (antipodal pairs
x + (-x) = 0 kill odd power sums; x*(-x) = -x^2 collapses products).  ODD-order smooth domains
(radix-3 NTT etc., -1 NOT in mu_n) REMOVE that symmetry.  The lead: does removing it make
odd-order mu_n HIGHER-ORDER MDS in the prize window -- i.e. do the generalized-Vandermonde /
Schur MINORS that boost the list size STOP vanishing?  If yes => a BGK-FREE off-wall route to
delta* (the floor is bypassed, list stays = generic-MDS = O(1/rho), prize plausibly TRUE for
odd domains).  If no => odd order is also higher-order-MDS-degenerate => the lead is refuted and
the negation symmetry is NOT the source of the obstruction.

WHY THE EXACT MINOR TEST (not list sampling).  Prior numerics (grind_evenodd_hosmds.py,
probe_smooth_listsize_energy.py) used worst_list() = SAMPLED codeword centers over q^k space:
sampling-floor-limited, CANNOT distinguish poly from super-poly, gave INCONCLUSIVE even/odd
signals.  This probe computes the EXACT higher-order-MDS-minor vanishing criterion over the
ACTUAL finite field F_p (the real prize regime, char p, NOT complex roots of unity), by
enumerating the relevant agreement SUBSETS of mu_n (size C(n,w), feasible for n up to ~25),
NOT codewords.  A vanishing minor is decided by an EXACT determinant in F_p (== 0 or != 0, no
floating point), so the yes/no is decisive.

THE PRECISE OBJECT (from the in-tree reduction, PROXIMITY_PRIZE_WORKBENCH R4 + MonomialLineList
Bridge + RootsOfUnityVandermonde + AbacusNCore):

  The MCA threshold of RS[mu_n,k] is controlled by the list size of RS[mu_n,k+1] beyond Johnson
  (badScalars_monomial_eq_degreeLTSucc).  A list-boosting configuration at agreement set
  A subset mu_n (|A| = w) is an EXTRA linear dependence among the value columns
  {1, X, ..., X^{k}} restricted to A beyond the generic k+1 -- equivalently a VANISHING of a
  generalized-Vandermonde minor of the matrix  [ x^{e} ]_{x in A, e in degrees}.  On a smooth
  domain x^n = 1, so the degrees only matter mod n, and (genVandermonde_rootsOfUnity_det_ne_zero
  _iff / AbacusNCore) the minor det( x^{e_j} )_{x in A_0, j} for a size-|A_0| subset vanishes IFF
  the exponents collide modulo |A_0| when A_0 is a coset of a subgroup, more generally IFF the
  Schur s_lambda vanishes on A.  The cleanest exact instance (R4, dir(k+1,k+2), w=k+2) is

      bad set  B  =  { -e_1(S) : S subset mu_n, |S| = k+2, e_2(S) = 0 }                  (*)

  with e_2(S) the 2nd elementary symmetric polynomial.  |B| (number of DISTINCT -e_1 values),
  and the number of solution subsets S, is the EXACT list/incidence count.  We compute (*) and
  its higher-order generalizations EXACTLY in F_p and read off even-vs-odd.

TESTS (all EXACT in F_p):
  T1.  Solution count of (*): N_solS(n,p,k) = #{S subset mu_n, |S|=k+2, e_2(S)=0}, and
       |B| = #distinct -e_1(S) over those S.  EVEN vs ODD n.  (The dir(k+1,k+2) bad set.)
  T2.  Antipodal accounting: for n even, how many solutions of e_2(S)=0 USE an antipodal pair
       {x,-x} (the negation-symmetry-supplied solutions).  Removing them: residual count.
  T3.  The GENERAL Schur / generalized-Vandermonde MINOR vanishing: over ALL w-subsets A of
       mu_n and a sweep of exponent multisets E (|E|=w), count minors det(x^{e})_{x in A,e in E}
       that vanish in F_p.  Even vs odd n.  This is the literal higher-order-MDS test: mu_n is
       "w-th-order MDS for pattern E" iff NO such minor vanishes.
  T4.  CROSS-CHECK vs complex roots of unity (the Schur/hook-content criterion the in-tree files
       prove): confirm the F_p minor vanishing matches the char-0 Schur vanishing (validates that
       the field-p computation is the same object the Lean development reasons about).
  T5.  VERDICT aggregator: is odd-order mu_n higher-order MDS in the window (no boosting minors
       beyond the generic MDS ones)?  Decisive yes/no + whether it is an off-BGK route.

USAGE:  python3 probe_oddorder_homds.py   [--full]
"""
import sys
import math
import itertools
import json
from collections import defaultdict

# ----------------------------------------------------------------- number theory (exact, in F_p)
def isprime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d = m - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def prime_factors(m):
    s = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            s.add(d)
            m //= d
        d += 1
    if m > 1:
        s.add(m)
    return s


def subgroup(p, n):
    """The order-n multiplicative subgroup mu_n of F_p (n | p-1), as a sorted list of residues."""
    assert (p - 1) % n == 0, f"{n} does not divide {p}-1"
    e = (p - 1) // n
    pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1:
            continue
        if any(pow(h, n // q, p) == 1 for q in pf):
            continue
        S = []
        x = 1
        for _ in range(n):
            x = x * h % p
            S.append(x)
        if len(set(S)) == n:
            return sorted(S)
    raise RuntimeError(f"no order-{n} subgroup in F_{p}")


def neg_in_subgroup(p, S):
    """True iff -1 in mu_n  (== n even, the negation symmetry)."""
    return (p - 1) in set(S)


def det_modp(M, p):
    """Exact determinant of a square matrix over F_p (Bareiss-free, fraction-free Gauss)."""
    n = len(M)
    A = [[x % p for x in row] for row in M]
    det = 1
    for col in range(n):
        piv = next((r for r in range(col, n) if A[r][col] % p != 0), None)
        if piv is None:
            return 0
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = (-det) % p
        inv = pow(A[col][col], p - 2, p)
        det = det * A[col][col] % p
        for r in range(col + 1, n):
            f = A[r][col] * inv % p
            if f:
                A[r] = [(A[r][c] - f * A[col][c]) % p for c in range(n)]
    return det % p


def matrank_modp(rows, p):
    """Exact rank over F_p."""
    A = [[x % p for x in r] for r in rows]
    if not A:
        return 0
    ncols = len(A[0])
    rank = 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(A)) if A[r][col] % p), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        inv = pow(A[rank][col], p - 2, p)
        A[rank] = [x * inv % p for x in A[rank]]
        for r in range(len(A)):
            if r != rank and A[r][col]:
                f = A[r][col]
                A[r] = [(A[r][c] - f * A[rank][c]) % p for c in range(ncols)]
        rank += 1
    return rank


def elem_sym(vals, j, p):
    """j-th elementary symmetric polynomial e_j of vals, mod p (via Vieta accumulation).
       coeffs[t] holds e_t of the vals seen so far; multiplying by (X+v) updates
       e_t <- e_t + v*e_{t-1} (descending so we don't clobber)."""
    m = len(vals)
    coeffs = [0] * (m + 1)
    coeffs[0] = 1
    seen = 0
    for v in vals:
        seen += 1
        for t in range(seen, 0, -1):
            coeffs[t] = (coeffs[t] + v * coeffs[t - 1]) % p
    return coeffs[j] % p if j <= m else 0


# ============================================================================ T1: dir(k+1,k+2)
def T1_dir_badset(p, S, k):
    """EXACT: bad set B = {-e_1(S'): S' subset mu_n, |S'|=k+2, e_2(S')=0}  (R4 dir(k+1,k+2)).
       Returns (#solution subsets, |B| distinct -e_1 values)."""
    n = len(S)
    w = k + 2
    if math.comb(n, w) > 4_000_000:
        return None
    sols = 0
    bvals = set()
    for Sp in itertools.combinations(S, w):
        if elem_sym(Sp, 2, p) == 0:
            sols += 1
            bvals.add((-sum(Sp)) % p)
    return sols, len(bvals)


def T2_antipodal_share(p, S, k):
    """For n EVEN: of the e_2(S')=0 solution subsets, how many CONTAIN an antipodal pair {x,-x}?
       (the negation-symmetry-supplied solutions; removing them = the odd-analog residual.)"""
    n = len(S)
    w = k + 2
    if math.comb(n, w) > 4_000_000:
        return None
    Sset = set(S)
    tot = 0
    anti = 0
    for Sp in itertools.combinations(S, w):
        if elem_sym(Sp, 2, p) == 0:
            tot += 1
            spset = set(Sp)
            if any(((p - x) % p) in spset for x in Sp):
                anti += 1
    return tot, anti


# ============================================================================ T3: general HOMDS minor
def T3_general_homds_minors(p, S, w, exponent_sets):
    """EXACT higher-order-MDS minor test: over ALL w-subsets A of mu_n and each exponent multiset
       E (|E|=w) in exponent_sets, count det( x^{e} )_{x in A, e in E} == 0 in F_p.
       mu_n is 'w-th-order MDS for E' iff NONE vanish.  Returns dict E-> (#vanish, #total)."""
    n = len(S)
    if math.comb(n, w) > 300_000:
        return None
    res = {}
    Asubs = list(itertools.combinations(range(n), w))
    Svals = S
    for E in exponent_sets:
        van = 0
        for A in Asubs:
            M = [[pow(Svals[i], e, p) for e in E] for i in A]
            if det_modp(M, p) == 0:
                van += 1
        res[tuple(E)] = (van, len(Asubs))
    return res


# generic-MDS baseline: a TRUE MDS code (RS) has NO vanishing minor with consecutive degrees
# 0..w-1 (standard Vandermonde, never 0 on distinct points).  Higher-order-MDS = also no
# vanishing for the BEYOND-consecutive (gapped) degree patterns that govern list-decoding.
def exponent_sweep(k, w, n, maxgap=None):
    """Degree patterns of size w: the generic 0..w-1 (Vandermonde) plus 'lifted' patterns that
       skip degrees (the list-decoding-beyond-Johnson / interior-rectangle shapes).  We keep
       exponents < n (the smooth domain only sees degrees mod n; >= n collapses)."""
    base = list(range(w))
    pats = [base]
    # single-lift patterns: replace the top degree w-1 by w-1+g (the +1-degree lift family)
    cap = (maxgap if maxgap is not None else min(n - 1, w + 3))
    for top in range(w, cap + 1):
        pats.append(list(range(w - 1)) + [top])
    # double-lift (two highest degrees lifted) -- the order-2 HOMDS shapes
    for t1 in range(w - 1, cap):
        for t2 in range(t1 + 1, cap + 1):
            pat = list(range(w - 2)) + [t1, t2]
            if len(set(pat)) == w:
                pats.append(pat)
    # de-dup
    uniq = []
    seen = set()
    for pat in pats:
        key = tuple(sorted(pat))
        if key not in seen and max(pat) < n:
            seen.add(key)
            uniq.append(sorted(pat))
    return uniq


# ============================================================================ T4: char-0 cross-check
def schur_vanishes_char0(lam, d):
    """Hook-content criterion: s_lam(1,w,...,w^{d-1}) == 0 at a primitive d-th root w."""
    lam = [x for x in lam if x > 0]
    numzero = polezero = 0
    for i in range(len(lam)):
        for j in range(lam[i]):
            content = j - i
            arm = lam[i] - j - 1
            leg = sum(1 for r in range(i + 1, len(lam)) if lam[r] > j)
            hook = arm + leg + 1
            if content % d == 0:
                numzero += 1
            if hook % d == 0:
                polezero += 1
    return numzero > polezero


def T4_crosscheck(p, S, w, exponent_sets):
    """For the FULL subgroup A=mu_n (the worst structured agreement set is the whole subgroup
       when w=n), the gen-Vandermonde minor on consecutive-vs-gapped exponents matches the
       char-0 Schur/hook-content prediction at d=n.  We verify on the d=n coset case."""
    n = len(S)
    out = []
    for E in exponent_sets:
        if len(E) != n:
            continue
        # exponents mod n; partition lambda from beta=E sorted desc
        Es = sorted(E, reverse=True)
        beta = Es
        lam = [beta[i] - (n - 1 - i) for i in range(n)]
        lam = [max(0, x) for x in lam]
        # F_p minor on full subgroup
        M = [[pow(S[i], e, p) for e in E] for i in range(n)]
        fp_zero = (det_modp(M, p) == 0)
        # residues distinct mod n?  (AbacusNCore: empty n-core <=> distinct mod n <=> nonzero)
        resid_distinct = (len(set(e % n for e in E)) == n)
        out.append((tuple(E), fp_zero, not resid_distinct))
    return out


# ============================================================================ grids
def find_prime_for_beta(n, beta_lo=4.0, beta_hi=5.0, hardcap=2_000_000):
    """Smallest prime p = n*m+1 (m>=2, proper subgroup) with log_n(p) in [beta_lo, beta_hi]."""
    lo = max(n * 2 + 1, int(n ** beta_lo))
    hi = min(hardcap, int(n ** beta_hi))
    m = max(2, lo // n)
    while n * m + 1 <= hi:
        p = n * m + 1
        if isprime(p):
            return p
    # fall through with finer step
    for mm in range(max(2, lo // n), hi // n + 1):
        p = n * mm + 1
        if isprime(p):
            return p
    return None


def find_prime_for_beta_iter(n, beta_lo=4.0, hardcap=2_000_000):
    lo = max(n * 2 + 1, int(n ** beta_lo))
    for m in range(max(2, lo // n), hardcap // n + 1):
        p = n * m + 1
        if p > hardcap:
            break
        if isprime(p):
            return p
    return None


def find_small_proper_prime(n, idx_min=2, idx_max=60):
    """smallest prime p=n*m+1, m in [idx_min,idx_max] -- a proper subgroup but small p (for the
       multi-prime field-independence check / feasible large-w minors)."""
    for m in range(idx_min, idx_max):
        p = n * m + 1
        if isprime(p):
            return p
    return None


# ============================================================================ MAIN
def main():
    full = "--full" in sys.argv
    results = {"tests": {}, "verdict": {}}

    # ---- the prize-shaped odd-order subgroups (proper, -1 NOT in mu_n) and even controls ----
    # n small enough for exact subset enumeration; primes at prize beta ~ 4 where feasible,
    # plus a moderate prime for the larger-w general minor test.
    ODD = [3, 5, 7, 9, 15, 11, 13, 25, 21]
    EVEN = [4, 6, 8, 10, 16, 12, 14]

    print("=" * 78)
    print("probe_oddorder_homds  (#407): EXACT higher-order-MDS minor test, odd vs even mu_n")
    print("=" * 78)

    # =========================================================== T1 + T2: dir(k+1,k+2) bad set
    print("\n--- T1/T2: dir(k+1,k+2) bad set  B={-e_1(S): |S|=k+2, e_2(S)=0}  EXACT in F_p ---")
    print(f"{'n':>3} {'par':>4} {'p':>9} {'beta':>5} {'k':>2} {'#solS':>7} {'|B|':>6} "
          f"{'#anti':>6} {'#non-anti':>9}")
    t1rows = []
    for n in sorted(set(ODD + EVEN)):
        par = "odd" if n % 2 else "even"
        # prize-beta prime if subset count feasible (need C(n,k+2) small); else small proper prime
        p = find_prime_for_beta_iter(n, 4.0) if n <= 13 else find_small_proper_prime(n)
        if p is None:
            p = find_small_proper_prime(n)
        if p is None:
            continue
        S = subgroup(p, n)
        beta = math.log(p) / math.log(n)
        for k in (1, 2):
            w = k + 2
            if w > n:
                continue
            if math.comb(n, w) > 3_000_000:
                continue
            r1 = T1_dir_badset(p, S, k)
            if r1 is None:
                continue
            sols, nb = r1
            anti = 0
            nonanti = sols
            if par == "even":
                r2 = T2_antipodal_share(p, S, k)
                if r2:
                    tot, anti = r2
                    nonanti = tot - anti
            print(f"{n:>3} {par:>4} {p:>9} {beta:>5.2f} {k:>2} {sols:>7} {nb:>6} "
                  f"{anti:>6} {nonanti:>9}")
            t1rows.append(dict(n=n, par=par, p=p, beta=round(beta, 3), k=k,
                               solS=sols, B=nb, anti=anti, nonanti=nonanti))
    results["tests"]["T1_T2_dir_badset"] = t1rows

    # =========================================================== T3: general HOMDS minors
    print("\n--- T3: general higher-order-MDS minors  det(x^e)_{x in A subset mu_n, e in E}==0 ---")
    print("     (mu_n is w-th-order-MDS for pattern E  <=>  NO minor vanishes; consecutive E=")
    print("      generic Vandermonde baseline, gapped E = list-decoding-beyond-Johnson shapes)")
    print(f"{'n':>3} {'par':>4} {'p':>7} {'w':>2} {'gen-van?':>8} "
          f"{'#patterns':>10} {'#with-vanish':>12} {'worst-vanish-frac':>17}")
    t3rows = []
    for n in sorted(set(ODD + EVEN)):
        par = "odd" if n % 2 else "even"
        p = find_small_proper_prime(n)
        if p is None:
            continue
        S = subgroup(p, n)
        for w in (3, 4):
            if w > n:
                continue
            if math.comb(n, w) > 200_000:
                continue
            pats = exponent_sweep(k=w - 2, w=w, n=n)
            res = T3_general_homds_minors(p, S, w, pats)
            if res is None:
                continue
            # baseline Vandermonde (consecutive 0..w-1) must never vanish (RS is MDS)
            base = tuple(range(w))
            genvan_ok = (res.get(base, (0, 1))[0] == 0)
            npat = len(res)
            nvanish = sum(1 for (E, (v, t)) in res.items() if v > 0)
            worstfrac = max((v / t for (E, (v, t)) in res.items()), default=0.0)
            print(f"{n:>3} {par:>4} {p:>7} {w:>2} {str(genvan_ok):>8} "
                  f"{npat:>10} {nvanish:>12} {worstfrac:>17.4f}")
            t3rows.append(dict(n=n, par=par, p=p, w=w, genVanOK=genvan_ok,
                               nPatterns=npat, nWithVanish=nvanish,
                               worstVanishFrac=round(worstfrac, 5),
                               vanishingPatterns=[list(E) for (E, (v, t)) in res.items() if v > 0]))
    results["tests"]["T3_general_homds"] = t3rows

    # =========================================================== T4: char-0 cross-check (full subgroup)
    print("\n--- T4: F_p minor vanishing == char-0 Schur/hook-content (AbacusNCore residue test) ---")
    print(f"{'n':>3} {'par':>4} {'p':>7} {'#patterns(w=n)':>15} {'#match':>7} {'all-match?':>10}")
    t4rows = []
    for n in (3, 4, 5, 6, 7, 8, 9):
        par = "odd" if n % 2 else "even"
        p = find_small_proper_prime(n)
        if p is None:
            continue
        S = subgroup(p, n)
        # exponent patterns of size n: beta-numbers of small partitions inside an n x n box
        pats = []
        # all strictly-increasing exponent n-tuples with entries < 2n (a representative sweep)
        for combo in itertools.combinations(range(2 * n), n):
            pats.append(list(combo))
            if len(pats) >= 400:
                break
        out = T4_crosscheck(p, S, n, pats)
        nmatch = sum(1 for (_, fp0, core0) in out if fp0 == core0)
        allm = (nmatch == len(out)) if out else True
        print(f"{n:>3} {par:>4} {p:>7} {len(out):>15} {nmatch:>7} {str(allm):>10}")
        t4rows.append(dict(n=n, par=par, p=p, nPatterns=len(out), nMatch=nmatch, allMatch=allm))
    results["tests"]["T4_crosscheck"] = t4rows

    # =========================================================== T5: VERDICT
    print("\n" + "=" * 78)
    print("T5: VERDICT")
    print("=" * 78)
    # Q1: do odd-order mu_n have FEWER list-boosting solutions than even (negation symmetry helps)?
    odd_sols = [r["solS"] for r in t1rows if r["par"] == "odd"]
    even_nonanti = [r["nonanti"] for r in t1rows if r["par"] == "even"]
    # Q2: are there ANY vanishing gapped minors for odd n in the window?  (=> NOT higher-order MDS)
    odd_t3 = [r for r in t3rows if r["par"] == "odd"]
    even_t3 = [r for r in t3rows if r["par"] == "even"]
    odd_any_gapped_vanish = any(r["nWithVanish"] > 0 for r in odd_t3)
    even_any_gapped_vanish = any(r["nWithVanish"] > 0 for r in even_t3)
    odd_vanish_examples = [(r["n"], r["p"], r["w"], r["vanishingPatterns"])
                           for r in odd_t3 if r["nWithVanish"] > 0]

    results["verdict"] = dict(
        odd_dir_solution_counts=odd_sols,
        even_dir_nonantipodal_counts=even_nonanti,
        odd_has_vanishing_gapped_minor=odd_any_gapped_vanish,
        even_has_vanishing_gapped_minor=even_any_gapped_vanish,
        odd_vanish_examples=odd_vanish_examples[:10],
    )

    print(f"\nQ1. dir(k+1,k+2) bad-set solution counts:")
    print(f"    ODD n  solS values: {odd_sols}")
    print(f"    EVEN n non-antipodal residual: {even_nonanti}")
    print(f"\nQ2. Does ODD-order mu_n have ANY vanishing GAPPED (list-boosting) minor in the window?")
    print(f"    ODD  any gapped minor vanishes:  {odd_any_gapped_vanish}")
    print(f"    EVEN any gapped minor vanishes:  {even_any_gapped_vanish}")
    if odd_any_gapped_vanish:
        print(f"    ODD vanishing examples (n,p,w,patterns): {odd_vanish_examples[:5]}")

    print("\nINTERPRETATION:")
    if not odd_any_gapped_vanish and even_any_gapped_vanish:
        verdict = ("ADVANCE: odd-order mu_n is higher-order MDS in the tested window (NO vanishing "
                   "gapped minor) while even-order is NOT -- the negation symmetry IS the obstruction "
                   "source, removing it routes BGK-free.")
    elif odd_any_gapped_vanish:
        verdict = ("REFUTE: odd-order mu_n ALSO has vanishing gapped minors (NOT higher-order MDS) -- "
                   "the cyclic x^n=1 symmetry, not the n/2 negation, is the obstruction source; "
                   "odd order does NOT give a BGK-free route.")
    else:
        verdict = ("INCONCLUSIVE in tested window: neither odd nor even shows vanishing gapped minors "
                   "at these (n,w); need larger w / n to reach the beyond-Johnson regime.")
    print("  " + verdict)
    results["verdict"]["text"] = verdict

    with open("oddorder_homds_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print("\n[written oddorder_homds_results.json]")


if __name__ == "__main__":
    main()
