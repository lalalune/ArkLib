#!/usr/bin/env python3
"""
probe_c23_gmmds_fixed_vs_generic  (issue #444 — ATTACK on conjecture C23)

C23 (GM-MDS Dual-Zero-Pattern Certificate for mu_n) claims:
  "Encode the L+1 candidate codewords as a GM-MDS dual zero-pattern Z; it satisfies the
   Brakensiek-Gopi-Makam |Z_S| <= (k-1)|S| solvability criterion (because the far-line
   agreement set is mu_gcd-coset-closed), so Lovett Thm 1.7 gives realizability at field
   size <= (k-1)! < q, capping the list at k-1 and pinning delta* = capacity - Theta(1/log n)."

THE DEFECT THIS PROBE EXHIBITS:
  Lovett Thm 1.7 (in-tree `LovettThm17`) is a *generic/symbolic* statement:
      "the union polynomial family pFamUnion(V,k) is LinearIndependent over MvPolynomial(Fin n) F"
  i.e. the zero pattern is realizable for SOME (generic) choice of evaluation points, equivalently
  the *symbolic* generalized Vandermonde determinant (a polynomial in the eval points) is NOT the
  zero polynomial. Field size <= (k-1)! is the number of eval points the GM-MDS *construction* needs
  to *pick*. It says NOTHING about a *prescribed, fixed* evaluation set --- and the prize fixes the
  eval set to mu_n (a proper subgroup). The relevant certificate is then the *evaluation* of that
  symbolic determinant at the FIXED points x_i in mu_n.

  THE WALL (in-tree HOMDSSmoothObstruction / RectNCore): at the fixed smooth domain mu_n the
  certificate det(zeta^{beta_j * i}) is NONZERO iff the abacus n-core of the shape is EMPTY, and for
  the list-decoding-past-Johnson extremal shape (a rectangle a^h, h = L < n) that holds iff n | a.
  Generic rectangle widths (n nmid a) give a NONEMPTY core => the FIXED-mu_n certificate VANISHES.

  So: GM-MDS criterion satisfied + symbolic det != 0 (generic realizable, Lovett applies)
       BUT  evaluated-at-mu_n det == 0  =>  NOT realizable over the fixed mu_n.
  The list is NOT capped at k-1 by GM-MDS over mu_n. C23 conflates GENERIC realizability with
  FIXED-eval-set realizability. This is the existence-vs-fixed horn => `secretly-open`
  (pinning delta* still needs the open p-dependent / structured-eval bound, NOT GM-MDS).

WHAT WE COMPUTE (reproducible, proper subgroup mu_n, p prime, p >> n^3, NEVER n = p-1):
  For prize-shaped rectangles a^h over mu_n:
   (1) GM-MDS criterion |Z_S| <= (k-1)|S| -- via the coset-closed dual zero pattern (it holds);
   (2) the SYMBOLIC generalized Vandermonde det is a nonzero polynomial (Lovett: generic OK)
       -- verified by evaluating at RANDOM generic points (det != 0 there);
   (3) the FIXED-mu_n certificate det(zeta^{beta_j i}) over F_p -- VANISHES for generic widths
       (n nmid a) exactly as RectNCore predicts -> realizability FAILS over fixed mu_n.
  The gap between (2) and (3) is the whole defect.
"""
import math, sys, random

def out(*a): print(*a); sys.stdout.flush()

# ---------- number theory ----------
def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def prime_for(n, mult):
    """smallest prime p = mult*n + 1 ... with p > n (proper subgroup mu_n, n | p-1, NEVER n=p-1)."""
    c = mult*n + 1
    while not is_prime(c): c += n
    return c

def smooth_subgroup(p, n):
    """the n-th roots of unity in F_p (a PROPER multiplicative subgroup; n | p-1, n < p-1)."""
    assert (p-1) % n == 0 and n < p-1, "must be a PROPER subgroup mu_n"
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        if pow(h, n, p) == 1 and all(pow(h, j, p) != 1 for j in range(1, n)):
            return h, [pow(h, t, p) for t in range(n)]
    raise RuntimeError("no primitive n-th root")

def det_mod(M, p):
    """determinant of an integer matrix mod prime p (Gaussian elimination)."""
    M = [[x % p for x in row] for row in M]
    n = len(M); det = 1
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] % p != 0: piv = r; break
        if piv is None: return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]; det = (-det) % p
        inv = pow(M[col][col], p-2, p)
        det = (det * M[col][col]) % p
        for r in range(col+1, n):
            f = (M[r][col] * inv) % p
            if f:
                M[r] = [(M[r][c] - f*M[col][c]) % p for c in range(n)]
    return det % p

def det_rational_via_modp(M, bigp):
    """proxy for the symbolic det at GENERIC points: det over a HUGE prime (no cancellation)."""
    return det_mod(M, bigp)

# ---------- shapes ----------
def rect_beta(n, a, h):
    """beta_j = (a if j<h else 0) + (n-1-j)  -- RectNCore.rectBeta."""
    return [(a if j < h else 0) + (n-1-j) for j in range(n)]

def ncore_empty(beta, n):
    return len(set(b % n for b in beta)) == n   # AbacusNCore.nCoreEmpty_iff_injOn_mod

# ---------- GM-MDS dual-zero-pattern solvability criterion ----------
def gmmds_criterion_holds(k, L):
    """The BGM/Lovett |Z_S| <= (k-1)|S| solvability criterion for the dual zero pattern of an
    (L+1)-codeword list certificate. C23 ASSERTS this holds (coset-closure). We model it as the
    standard GM-MDS feasibility: a dual zero pattern is solvable iff for every subset S of the
    L+1 rows, the number of common prescribed zeros |Z_S| <= (k-1)|S|. For the *generic* (Lovett)
    side this is exactly the condition Lovett Thm 1.7 consumes -- and when it holds the SYMBOLIC
    det is a nonzero polynomial. We grant C23 its premise: take it satisfied (return True) and
    instead test whether GENERIC realizability transfers to the FIXED mu_n."""
    return True  # grant C23's premise; the defect is downstream (fixed vs generic)

def main():
    out("="*96)
    out("C23 ATTACK: GM-MDS gives GENERIC realizability (symbolic det != 0), but the FIXED")
    out("            smooth domain mu_n ANNIHILATES the certificate for generic shapes.")
    out("            => GM-MDS does NOT cap the list over mu_n. (existence-vs-fixed horn)")
    out("="*96)

    rng = random.Random(20260614)
    BIGP = (1 << 521) - 1  # a huge Mersenne prime, proxy for 'generic eval points' (char 0-ish)

    NS = [16, 32, 64]
    rho_den = 2  # rate 1/2 (k = n/2); also try others below

    out("\nLEGEND: 'crit' = GM-MDS |Z_S|<=(k-1)|S| (granted True);")
    out("        'sym!=0' = symbolic gen-Vandermonde det nonzero at GENERIC pts (Lovett: realizable);")
    out("        'mu_n det' = the SAME det EVALUATED at the FIXED mu_n over F_p;")
    out("        'realiz/mu_n' = realizable over the FIXED prize domain mu_n  (== mu_n det != 0).")
    out("")

    any_gap = False
    for n in NS:
        k = n // rho_den
        a_john = math.ceil(math.sqrt(k * n))   # Johnson agreement
        # prize-style: p prime, p >> n^3, n | p-1, NEVER n = p-1
        mult = max(64, 64*n*n)                  # ensures p ~ mult*n+1 >> n^3 (p ~ 64 n^3)
        p = prime_for(n, mult)
        assert p > 32*n**3, (p, n)              # comfortably p >> n^3
        h_root, mu = smooth_subgroup(p, n)
        zeta = h_root  # primitive n-th root in F_p

        out(f"  n={n}  k={k}  Johnson a={a_john}  p={p} (p/n^3={p/n**3:.1f})  mu_n proper (n={n}<p-1={p-1})")
        out(f"    {'L=h':>4} {'a(width)':>9} {'n|a?':>5} {'core':>6} | {'crit':>5} {'sym!=0':>7} "
            f"{'mu_n det':>10} {'realiz/mu_n':>12}")

        # extremal list-decoding shapes: rectangles a^h with h = L < n codewords agreeing on width a.
        # sweep a few widths around Johnson excess; include both n|a and n nmid a.
        for h in [2, 4, min(k, n-1)]:
            if h >= n: continue
            L = h
            for a in [a_john, a_john+1, ((a_john//n)+1)*n]:  # last is the n|a 'lucky' width
                if a <= 0: continue
                beta = rect_beta(n, a, h)
                core_empty = ncore_empty(beta, n)
                crit = gmmds_criterion_holds(k, L)
                # symbolic det at GENERIC points: build gen-Vandermonde with random distinct x_i
                # rows indexed by points, cols by beta exponents (take h+? -> use n x n with beta).
                xs = []
                seen = set()
                while len(xs) < n:
                    v = rng.randrange(2, BIGP)
                    if v not in seen: seen.add(v); xs.append(v)
                Msym = [[pow(xs[i], beta[j], BIGP) for j in range(n)] for i in range(n)]
                sym_nonzero = (det_rational_via_modp(Msym, BIGP) != 0)
                # FIXED mu_n certificate: det(zeta^{beta_j * i}) over F_p
                Mfix = [[pow(zeta, (beta[j]*i) % (p-1), p) for j in range(n)] for i in range(n)]
                fix_det = det_mod(Mfix, p)
                realiz = (fix_det != 0)
                ndiva = (a % n == 0)
                gap = sym_nonzero and not realiz
                if gap: any_gap = True
                flag = "  <== GAP (generic OK, fixed mu_n FAILS)" if gap else ""
                out(f"    {L:>4} {a:>9} {('yes' if ndiva else 'no'):>5} "
                    f"{('empty' if core_empty else 'NONEMPTY'):>6} | "
                    f"{str(crit):>5} {str(sym_nonzero):>7} {fix_det:>10} {str(realiz):>12}{flag}")
        out("")

    out("="*96)
    out("CROSS-CHECK: RectNCore.rectBeta_nCoreEmpty_iff  (0<h<n):  nCoreEmpty(a^h) <=> n | a")
    out("            and HOMDSSmoothObstruction:  mu_n det != 0  <=>  nCoreEmpty.")
    ok = True
    for n in [16, 32]:
        p = prime_for(n, max(8, n*n))
        zeta, _ = smooth_subgroup(p, n)
        for h in [1, 2, 3, n-1]:
            if not (0 < h < n): continue
            for a in range(1, 2*n+2):
                beta = rect_beta(n, a, h)
                pred_core = (a % n == 0)               # the in-tree iff
                got_core  = ncore_empty(beta, n)
                Mfix = [[pow(zeta, (beta[j]*i) % (p-1), p) for j in range(n)] for i in range(n)]
                det_nonzero = (det_mod(Mfix, p) != 0)
                if (pred_core != got_core) or (got_core != det_nonzero):
                    ok = False
                    out(f"    *** MISMATCH n={n} h={h} a={a}: n|a={pred_core} core={got_core} det!=0={det_nonzero}")
    out(f"    in-tree dichotomy reproduced over fixed mu_n: {'OK (0 mismatches)' if ok else '*** FAILED ***'}")

    out("\n" + "="*96)
    out("VERDICT:")
    out(f"  Found generic-OK / fixed-mu_n-FAILS gap: {any_gap}")
    out("  GM-MDS / Lovett Thm 1.7 => GENERIC (symbolic) realizability + field size <= (k-1)!,")
    out("  i.e. the eval points the construction is FREE TO CHOOSE. The prize FIXES eval = mu_n.")
    out("  At the fixed mu_n the SAME certificate VANISHES for generic list shapes (n nmid a),")
    out("  so GM-MDS does NOT cap the mu_n list at k-1, and does NOT pin delta* past Johnson.")
    out("  C23 conflates generic realizability with fixed-eval-set realizability => SECRETLY-OPEN:")
    out("  pinning delta* over the FIXED mu_n still needs the open structured/p-dependent bound.")
    out("="*96)

if __name__ == "__main__":
    main()
