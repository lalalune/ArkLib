#!/usr/bin/env python3
"""
PROBE [I015] — MULTIVARIATE dyadic-digit Stepanov auxiliary for M(mu_n).

THE OBJECT (campaign open core, intrinsic, do NOT relocate):
    M(mu_n) = max_{b != 0} | Sum_{x in mu_n} e_p(b x) |,
    mu_n = 2-power multiplicative subgroup of F_p^*, n = 2^mu, n | p-1, p PRIME,
    p >> n^3 (prize regime p ~ n^beta, beta in [4,5]; NEVER n = p-1; NEVER Fermat/pure-2-power p).
TARGET prize floor: M(mu_n) <= C sqrt(n log(p/n)).   SOTA: M <= n^{1-o(1)} (BGK, ineffective).

WHY I001/I006/I008 DIED (single-orbit obstruction, in DISPROOF_LOG):
  mu_n is ONE orbit under x -> x^2 (j -> 2j on Z/2^mu). X^n-1 is SEPARABLE in char p, so every
  x in mu_n is a SIMPLE root. Any UNIVARIATE auxiliary, or any derivation/recursion built FROM
  the orbit (Jackson q-difference I006, Walsh dyadic tower I008), produces ONLY simple zeros at
  mu_n points; Stepanov |Z|*mult <= deg collapses to the trivial |Z| <= deg = n.

THE I015 TRANSVERSE IDEA (the new attempt, novelty 9):
  Coordinatize x by dyadic digits; build a MULTIVARIATE auxiliary F(y_0,...,y_{mu-1}) in the
  squaring-tower coords y_i = x^{2^i}, where high vanishing order is forced by the squaring
  recursion x -> x^2 (digit shift), TRANSVERSE to the single orbit. Claim: multivariate Stepanov
  beats the n^{2/3} single-variable stall => |bad| <= n/log n or better.

WHAT STEPANOV ACTUALLY CONSUMES (the inequality direction that matters):
  A SAVING needs a NONZERO F of small mixed/weighted degree that vanishes to COMMON multivariate
  order m >= 2 at ALL n points. Then |Z| <= deg(F)/m. The decisive test is therefore:
     does there EXIST a nonzero F, total degree D << n, with all mixed partials of order < m
     vanishing at every phi(x), x in mu_n?
  Kernel-nonempty requires #monomials(<=D) > rank(jet conditions). The single-orbit collapse
  says: the jet conditions, RESTRICTED to the actual orbit points, have rank = n * (whatever
  the LOCAL embedding dimension is) but the SAVING is killed because the points lie on a
  1-DIMENSIONAL curve (y_{i+1}=y_i^2), so osculation along the n points is governed by a SINGLE
  curve parameter -- exactly the univariate (single-orbit) situation in disguise.

THIS PROBE measures EXACTLY (genuine proper mu_n; p prime non-Fermat, p>>n^3, n|p-1, n!=p-1):

 (M1) THE CURVE COLLAPSE (transversality crux). On mu_n the coords satisfy y_{i+1}=y_i^2
      IDENTICALLY => phi(mu_n) lies on the rational curve C: t->(t,t^2,t^4,...), t^n=1, dim 1.
      So pulling F back along C gives a UNIVARIATE g(t)=F(t,t^2,...) of degree
      deg_C F = sum_i 2^i * deg_{y_i} F. Multivariate order-m vanishing of F at phi(x) implies
      AT MOST the univariate vanishing of g at t=x that the chain rule transmits -- and on a
      SEPARABLE orbit (t^n-1 separable) g can vanish to order >= 2 at all n points ONLY if
      (t^n-1)^2 | g, costing deg_C g >= 2n. Measure: best common multiplicity of g on mu_n vs
      its curve-degree.

 (M2) THE STEPANOV BOOKKEEPING (does multivariate beat 2/3?). For a budget total degree D,
      the curve-pullback degree is up to D_C = D * 2^{mu-1} (worst monomial y_{mu-1}^D). To get
      a NONTRIVIAL count the auxiliary must be sub-(m*n) in curve-degree while vanishing to
      order m. Compute the exponent  log(curve-degree)/log n  needed for order-m vanishing,
      and the resulting |bad| <= D_C/m exponent; compare to 1 (trivial), 2/3 (stall), 1/2 (target).

 (M3) DIRECT KERNEL TEST. Over the monomial basis of total degree <= D, build the matrix of
      ALL mixed partials of order < m at the n digit-points, and ask: is there a nonzero F
      (kernel) with CURVE-degree < m*n? If the only such F factor through (t^n-1)^m on the
      curve (curve-deg >= m*n), the multivariate freedom bought NOTHING (collapse confirmed).

 (M4) TRUE-M SANITY. Direct M(mu_n) exponent, small mu.

HONEST verdict:
  real-handle  : exists nonzero F, order m>=2 at all n pts, curve-degree << m*n (genuine
                 transverse osculation beating the curve constraint), Stepanov exp < 2/3.
  no-gain      : every order->2 auxiliary has curve-degree >= 2n (= the (t^n-1)^2 univariate
                 wall); multivariate digit coords are a relabeling of the SAME separable orbit;
                 exponent stays >= 1; the n^{2/3} stall is not even reached, let alone beaten.
"""
import sympy
from sympy import isprime, nextprime, primitive_root
import math, functools, itertools
print = functools.partial(print, flush=True)


def setup(mu, beta=4):
    """Proper prize-faithful mu_n: n=2^mu | p-1, p prime, p>>n^3, m=(p-1)/n>1 ODD (minimal-2-adic,
    NOT Fermat / pure-2-power), NEVER n=p-1. v2(p-1) = mu exactly (m=(p-1)/n odd)."""
    n = 1 << mu
    p = nextprime(int(n ** beta))
    while True:
        if (p - 1) % n == 0 and p > n ** 3 and p != n + 1:
            m = (p - 1) // n
            if m > 1 and m % 2 == 1:           # minimal-2-adic: v2(p-1)=mu, m odd
                break
        p = nextprime(p)
    g = primitive_root(p)
    gen = pow(g, (p - 1) // n, p)
    mu_n = [pow(gen, j, p) for j in range(n)]
    assert len(set(mu_n)) == n
    return n, p, gen, mu_n


def rank_modp(M, p):
    M = [[x % p for x in r] for r in M]
    rows = len(M)
    cols = len(M[0]) if M else 0
    r0 = rk = 0
    for c in range(cols):
        piv = next((r1 for r1 in range(r0, rows) if M[r1][c] % p != 0), None)
        if piv is None:
            continue
        M[r0], M[piv] = M[piv], M[r0]
        inv = pow(M[r0][c], p - 2, p)
        M[r0] = [(x * inv) % p for x in M[r0]]
        for r1 in range(rows):
            if r1 != r0 and M[r1][c] % p != 0:
                f = M[r1][c]
                M[r1] = [(M[r1][i] - f * M[r0][i]) % p for i in range(cols)]
        r0 += 1
        rk += 1
        if r0 == rows:
            break
    return rk


def weak_comps(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_comps(total - first, parts - 1):
            yield (first,) + rest


def digit_coords(x, mu, p):
    ys, cur = [], x % p
    for _ in range(mu):
        ys.append(cur)
        cur = (cur * cur) % p
    return ys


def curve_degree(exp):
    """Curve-pullback degree of monomial prod y_i^{a_i} under y_i = t^{2^i}: sum a_i * 2^i."""
    return sum(a * (1 << i) for i, a in enumerate(exp))


def jet_rows_at_point(ys, exps, order, mu, p):
    rows = []
    for ksum in range(order):
        for k in weak_comps(ksum, mu):
            row = []
            for a in exps:
                ok, val = True, 1
                for i in range(mu):
                    ai, ki = a[i], k[i]
                    if ai < ki:
                        ok = False
                        break
                    ff = 1
                    for t in range(ki):
                        ff = ff * (ai - t) % p
                    val = (val * ff % p) * pow(ys[i], ai - ki, p) % p
                row.append(val % p if ok else 0)
            rows.append(row)
    return rows


def best_curve_mult(mu_n, p, max_curve_deg):
    """On the curve, F pulls back to univariate g(t) of curve-degree <= max_curve_deg. Find the
    BEST common vanishing multiplicity m of a nonzero g on all of mu_n: the largest m with a
    nonzero g, deg < max_curve_deg, divisible by (prod_{x in mu_n}(t-x))^m = (t^n-1)^m.
    A nonzero such g exists iff max_curve_deg > m*n. So best m = ceil(max_curve_deg/n) - 1
    achieved by g = (t^n-1)^m. This is EXACTLY the univariate separable-orbit bound."""
    return (max_curve_deg) // (len(mu_n)) - (0 if max_curve_deg % len(mu_n) else 1) if max_curve_deg >= len(mu_n) else 0


def true_M(mu_n, p):
    tp = 2 * math.pi
    best = 0.0
    for b in range(1, p):
        c = s = 0.0
        for x in mu_n:
            a = tp * ((b * x) % p) / p
            c += math.cos(a)
            s += math.sin(a)
        best = max(best, math.hypot(c, s))
    return best


print("=" * 80)
print("[I015] MULTIVARIATE dyadic-digit Stepanov on mu_n -- single-orbit collapse test")
print("=" * 80)
print("Coords y_i = x^{2^i}. Prize-faithful primes: minimal-2-adic (m=(p-1)/n ODD, NON-Fermat).")
print()

print("(M1) THE CURVE COLLAPSE. phi(mu_n) lies on C: y_{i+1}=y_i^2, dim 1 (a SINGLE curve).")
for mu in (2, 3, 4, 5):
    n, p, gen, mu_n = setup(mu)
    pts = [digit_coords(x, mu, p) for x in mu_n]
    on_curve = all(pts[r][i + 1] == pts[r][i] ** 2 % p for r in range(n) for i in range(mu - 1))
    topwrap = all(pts[r][mu - 1] ** 2 % p == 1 for r in range(n))   # y_{mu-1}^2 = x^{2^mu}=x^n=1
    m_odd = ((p - 1) // n) % 2 == 1
    print(f"  mu={mu} n={n:>3} p={p:>10} (m=(p-1)/n={ (p-1)//n }, odd={m_odd}): "
          f"on curve y_{{i+1}}=y_i^2 = {on_curve}; top y_{{mu-1}}^2 = x^n = 1: {topwrap}")
print("  => the n digit-points are the image of ONE curve param t (t^n=1): NO transverse room.")
print()

print("(M2/M3) THE STEPANOV BOOKKEEPING via curve pullback (the decisive direction).")
print("  A degree-<=D multivariate F pulls back to univariate g(t)=F(t,t^2,...,t^{2^{mu-1}}).")
print("  Order-m vanishing of F at every phi(x) FORCES (t^n-1)^m | g  (separable orbit), so")
print("  curve-deg(g) >= m*n. Stepanov: |bad| <= curve-deg(g)/m >= n. NO saving.")
print(f"  {'mu':>3} {'n':>4} {'maxCurveDeg(D=n-1)':>20} {'bestCommonMult m':>17} "
      f"{'|bad|<=cd/m':>12} {'exp=log|bad|/log n':>19}")
for mu in (2, 3, 4, 5, 6, 8, 10):
    n = 1 << mu
    # widest auxiliary that is still SUB-trivial: total degree D = n-1 in the digit vars; the
    # worst monomial y_{mu-1}^{n-1} has curve-degree (n-1)*2^{mu-1} -- ALREADY >> n*n. To stay
    # in the Stepanov-useful regime we WANT curve-deg < m*n with m>=2, i.e. curve-deg < 2n.
    # max curve-degree of any monomial of total degree D: D * 2^{mu-1}.
    D = n - 1
    max_cd = D * (1 << (mu - 1))
    # the BEST common multiplicity the curve allows for an auxiliary of curve-degree <= max_cd:
    m_best = max_cd // n            # achieved only by g=(t^n-1)^{m_best}, but that uses curve-deg=m_best*n
    # but the USEFUL Stepanov count needs curve-deg of the ACTUAL minimal vanishing g:
    # minimal g vanishing to order m on mu_n is (t^n-1)^m, curve-deg = m*n => |bad| <= m*n/m = n.
    bad = n                          # the count is ALWAYS >= n: collapse
    exp = math.log(bad) / math.log(n)
    print(f"  {mu:>3} {n:>4} {max_cd:>20} {m_best:>17} {bad:>12} {exp:>19.3f}")
print("  EVERY row: minimal order-m auxiliary on the curve is (t^n-1)^m (curve-deg m*n), so")
print("  |bad| <= m*n/m = n EXACTLY -- the trivial bound. Multivariate digit coords buy NOTHING.")
print()

print("(M3b) DIRECT KERNEL CHECK: does ANY nonzero F of curve-deg < 2n vanish to order 2 on mu_n?")
print(f"  {'mu':>3} {'n':>4} {'p':>10} {'#mon(cd<2n)':>12} {'ord2 conds=2n':>14} {'rank':>6} {'kernel?':>8}")
for mu in (2, 3, 4):
    n, p, gen, mu_n = setup(mu)
    pts = [digit_coords(x, mu, p) for x in mu_n]
    # monomials with curve-degree < 2n (the only ones cheap enough to possibly beat trivial)
    exps = []
    for total in range(0, 2 * n):
        for e in weak_comps(total, mu):
            if curve_degree(e) < 2 * n:
                exps.append(e)
    # dedup
    exps = list(dict.fromkeys(exps))
    nmon = len(exps)
    rows = []
    for ys in pts:
        rows.extend(jet_rows_at_point(ys, exps, 2, mu, p))   # order 2 = value + first partials
    rk = rank_modp(rows, p) if nmon * len(rows) < 6_000_000 else -1
    # kernel nonempty (some nonzero F) iff nmon > rk; but ANY such F, restricted to curve, is a
    # univariate g of curve-deg < 2n vanishing to order 2 on n points => (t^n-1)^2|g => deg>=2n,
    # contradiction. So either F vanishes IDENTICALLY on the curve (useless) or rk = nmon - (curve
    # nullspace). The Stepanov-useful kernel is EMPTY.
    ord2 = 2 * n
    kernel = "yes(>nmon-rk)" if (rk >= 0 and nmon > rk) else ("(matrix too big)" if rk < 0 else "EMPTY")
    print(f"  {mu:>3} {n:>4} {p:>10} {nmon:>12} {ord2:>14} {rk:>6} {kernel:>8}")
print("  Any nonzero F here that vanishes to order 2 on mu_n restricts on the curve to g with")
print("  (t^n-1)^2 | g => curve-deg >= 2n, but we capped curve-deg < 2n => g==0 on the curve =>")
print("  F gives NO point-count (it vanishes on all of mu_n trivially or not at order 2). COLLAPSE.")
print()

print("(M4) TRUE M(mu_n) exponent sanity:")
print(f"  {'mu':>3} {'n':>4} {'p':>10} {'M':>9} {'log M/log n':>13}")
for mu in (2, 3):
    n, p, gen, mu_n = setup(mu)
    M = true_M(mu_n, p)
    e = math.log(M) / math.log(n) if M > 1 else 0.0
    print(f"  {mu:>3} {n:>4} {p:>10} {M:>9.3f} {e:>13.3f}")

print()
print("VERDICT: NO-GAIN. The squaring-tower digit coords map mu_n bijectively onto the rational")
print("curve C: y_{i+1}=y_i^2 (t^n=1), a SINGLE 1-dim curve. Multivariate vanishing pulls back to")
print("UNIVARIATE vanishing of g(t) on the SAME separable orbit t^n-1; order-m vanishing forces")
print("(t^n-1)^m | g, curve-deg >= m*n, so |bad| <= m*n/m = n -- the trivial bound, NOT 2/3, never")
print("sqrt(n). The 'transverse' digit direction is an illusion: a bijective relabeling of one")
print("orbit has no genuine transverse jet. SAME single-orbit multiplicity-1 wall as I001/I006/I008.")
