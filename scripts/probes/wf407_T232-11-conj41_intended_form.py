#!/usr/bin/env python3
"""
wf407_T232-11-conj41_intended_form.py
=====================================
Thread T232-11-conj41 (#407): Conjecture 41 (Chai-Fan, ePrint 2026/858, c>=3
"open-set rank lemma") -- WHICH printed form is INTENDED, and does the correct
form survive / give a usable list bound, or weld onto the PTE / Gauss-period wall?

PRIOR STATE (DISPROOF_LOG O42/O43/O44/O64, KB deltastar-407-conj41-escape-clause,
sweep_A31_conj41.py): the printed "Equivalently, M_true <= floor((2D-1)/c)" form
is REFUTED (machine-checked conj41_violation_witness / conj41_mtrue_witness over
ZMod 17; integer fiber spread M_true=9 > 5 at n=14, w=6, c=3) on the ADDITIVE
domain {0,..,N-1}. The two printed forms (rank/dichotomy vs the count "Equivalently"
sentence) are INEQUIVALENT. The (ii)=(iii) weld via class syndromes ties the count
form to the PTE / esymm-fiber wall.

WHAT THIS PROBE DECIDES (two sharp gaps the prior work left open):

  GAP A -- WHICH FORM IS INTENDED.
    The refuted object M_compat / M_true counts compatible LINE-PARAMETERS gamma on
    a syndrome LINE s(gamma)=s1+gamma*u_top.  But the quantity that feeds FRI
    soundness / the deep-quotient transfer is the WORST-CASE LIST at a *FIXED*
    syndrome -- the number of weight-w supports E compatible with ONE syndrome s
    (= dim of the relevant kernel / # codewords near a received word).  These are
    DIFFERENT.  We measure BOTH:
      M_line(s1,u)   = #{ gamma : exists compatible support on s1+gamma*u }  (refuted obj)
      M_fixed(s)     = #{ weight-w supports E : CompatC(s,c,E) }  at a single s (intended obj)
    and ask: does M_fixed stay <= floor((2D-1)/c) where M_line exceeds it?  If yes,
    the rank/dichotomy (fixed-syndrome) form is the INTENDED one and the
    "Equivalently" sentence is an ERRATUM (count-over-line != fixed-syndrome count).

  GAP B -- THE PRIZE DOMAIN IS MULTIPLICATIVE mu_n, not additive {0..N-1}.
    Re-run the genuine-M_true spread on mu_n (n-th roots of unity in F_p, p=1 mod n,
    prize-shaped p~n^4) and on a generic multiplicative subset, to see whether the
    refutation is an additive-domain artifact or survives on the prize domain.
    If M_fixed grows on mu_n -> the correct form WELDS onto the PTE/esymm-fiber wall
    (= A21/A08 = additive-energy / Gauss-period core).  If M_fixed stays O(1) on mu_n
    while M_line grows -> the rank form SURVIVES and gives a usable list bound.

All arithmetic is EXACT (integer / mod-p, no sampling).  Decisive at enumerable n.
"""

import itertools
from collections import defaultdict

# ---------------------------------------------------------------------------
# self-contained number theory (no sympy dependency)
# ---------------------------------------------------------------------------

def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def nextprime(n):
    n = int(n) + 1
    while not is_prime(n):
        n += 1
    return n

def _factorize(n):
    fac = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            fac[d] = fac.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fac[n] = fac.get(n, 0) + 1
    return fac

def primitive_root(p):
    """a primitive root mod prime p."""
    phi = p - 1
    fac = list(_factorize(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root found")

# ---------------------------------------------------------------------------
# exact symmetric functions, locator, syndrome pairing
# ---------------------------------------------------------------------------

def esymm(support, j, p=None):
    if j == 0:
        return 1
    acc = 0
    for combo in itertools.combinations(support, j):
        prod = 1
        for x in combo:
            prod *= x
            if p is not None:
                prod %= p
        acc += prod
        if p is not None:
            acc %= p
    return acc if p is None else acc % p

def locator_coeffs(E, p=None):
    """coeffs low->high of prod_{a in E}(X-a), length |E|+1."""
    coeffs = [1]
    for a in E:
        if p is not None:
            a %= p
        new = [0] * (len(coeffs) + 1)
        for i, ci in enumerate(coeffs):
            new[i] = new[i] - a * ci
            new[i + 1] = new[i + 1] + ci
            if p is not None:
                new[i] %= p
                new[i + 1] %= p
        coeffs = new
    return coeffs

def synd(s, N, coeffs, p):
    """<P, s> = sum_{j<N} P_j s_j  with P given by its coeff list."""
    acc = 0
    for j in range(N):
        cj = coeffs[j] if j < len(coeffs) else 0
        acc += cj * s[j]
    return acc % p

def syndr_value(E, r, s, N, p):
    """<X^r * Lambda_E, s> over F_p."""
    base = locator_coeffs(E, p)
    coeffs = [0] * r + base
    return synd(s, N, coeffs, p)

def compat_fixed(E, s, N, c, p):
    """CompatC(s,c,E): <X^r Lambda_E, s> = 0 for all r < c."""
    for r in range(c):
        if syndr_value(E, r, s, N, p) != 0:
            return False
    return True

def error_values_nonzero(E, p):
    """genuine list element <=> all Vandermonde error values prod_{y!=x}(x-y) nonzero."""
    El = list(E)
    for x in El:
        prod = 1
        for y in El:
            if y == x:
                continue
            d = (x - y) % p
            if d == 0:
                return False
            prod = (prod * d) % p
        if prod == 0:
            return False
    return True

# ---------------------------------------------------------------------------
# class-syndrome construction (the O43 witness mechanism, exact)
# top-direction line through the class of fixed (e_1..e_{c-1}):
#   on s(gamma)=s1+gamma*u_top the gamma-free eqns are e_1..e_{c-1}=class,
#   gamma is affine in e_c.  We build s1 directly from the class so that
#   compat_fixed(E, s1, ...) <=> e_1..e_c(E) = class values.
# Newton: <X^r Lambda_E, s1> for s1=(0..0,h0,..,h_{c}) equals e_{r+1}-class_{r+1}
# up to the convolution; we sidestep by enumerating fibers directly.
# ---------------------------------------------------------------------------

def class_fiber(L, w, c, p):
    """partition weight-w supports by (e_1..e_{c-1}) class (the gamma-free window)."""
    classes = defaultdict(list)
    for E in itertools.combinations(L, w):
        key = tuple(esymm(E, j, p) for j in range(1, c))
        classes[key].append(E)
    return classes

def M_line_genuine(supports, c, p):
    """refuted object: # distinct e_c over genuine supports in this class
    = # distinct compatible line-parameters gamma (O44 decoupling)."""
    vals = set()
    for E in supports:
        if error_values_nonzero(E, p):
            vals.add(esymm(E, c, p))
    return len(vals)

def M_fixed_genuine(supports, c, p):
    """INTENDED object: max over e_c-VALUES of the # genuine supports sharing the
    FULL (e_1..e_c) class -- i.e. the list at a *fixed* syndrome (not a line).
    This is the worst-case fixed-syndrome list size = the FRI/deep-quotient quantity."""
    byec = defaultdict(int)
    for E in supports:
        if error_values_nonzero(E, p):
            byec[esymm(E, c, p)] += 1
    return max(byec.values()) if byec else 0

# ---------------------------------------------------------------------------
# domains
# ---------------------------------------------------------------------------

def prize_prime(n):
    """smallest prime p > n^4 (and > 1009) with p == 1 mod n (RS smooth-domain shape)."""
    p = nextprime(max(n ** 4, 1009))
    tries = 0
    while (p - 1) % n != 0 and tries < 2000:
        p = nextprime(p)
        tries += 1
    return p

def mu_n(n, p):
    """the n-th roots of unity in F_p (requires n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, i, p) % p for i in range(n)]

def banner(s):
    print("\n" + "=" * 78)
    print(s)
    print("=" * 78)

# ---------------------------------------------------------------------------
# GAP A : M_line (refuted) vs M_fixed (intended), on the additive O43 domain
# ---------------------------------------------------------------------------

def expA_line_vs_fixed(Ns, w, c):
    banner(f"GAP A  M_line (refuted count-over-line) vs M_fixed (intended fixed-syndrome list)"
           f"   w={w} c={c}")
    D = w + c
    ceil = (2 * D - 1) // c
    print(f"  additive domain L={{0..N-1}};  D={D}  ceiling floor((2D-1)/c)={ceil}")
    print(f"  {'N':>4} {'p~N^4':>9} {'M_line':>7} {'M_fixed':>8} {'line>ceil':>10} {'fixed>ceil':>11}")
    for N in Ns:
        L = list(range(N))
        p = prize_prime(N)
        cls = class_fiber(L, w, c, p)
        mline = max((M_line_genuine(s, c, p) for s in cls.values()), default=0)
        mfix = max((M_fixed_genuine(s, c, p) for s in cls.values()), default=0)
        print(f"  {N:>4} {p:>9} {mline:>7} {mfix:>8} "
              f"{('YES' if mline>ceil else 'no'):>10} {('YES' if mfix>ceil else 'no'):>11}")

# ---------------------------------------------------------------------------
# GAP B : the MULTIPLICATIVE prize domain mu_n  (vs additive)
# ---------------------------------------------------------------------------

def expB_mun_domain(ns, w, c):
    banner(f"GAP B  prize domain mu_n  (n-th roots of unity),  w={w} c={c}")
    D = w + c
    ceil = (2 * D - 1) // c
    print(f"  D={D}  ceiling floor((2D-1)/c)={ceil}   (n MUST be >= w to host weight-w supports)")
    print(f"  {'n':>4} {'p':>11} {'M_line':>7} {'M_fixed':>8} {'line>ceil':>10} {'fixed>ceil':>11} {'#cls':>6}")
    for n in ns:
        if n < w:
            continue
        p = prize_prime(n)
        L = mu_n(n, p)
        cls = class_fiber(L, w, c, p)
        mline = max((M_line_genuine(s, c, p) for s in cls.values()), default=0)
        mfix = max((M_fixed_genuine(s, c, p) for s in cls.values()), default=0)
        print(f"  {n:>4} {p:>11} {mline:>7} {mfix:>8} "
              f"{('YES' if mline>ceil else 'no'):>10} {('YES' if mfix>ceil else 'no'):>11} {len(cls):>6}")

def expB_mun_vs_additive(n, w, c):
    """side-by-side at the same n: additive {0..n-1} vs multiplicative mu_n, same prize prime."""
    banner(f"GAP B'  additive vs multiplicative at SAME n  (n={n}, w={w}, c={c})")
    D = w + c
    ceil = (2 * D - 1) // c
    p = prize_prime(n)
    for name, L in [("additive {0..n-1}", list(range(n))),
                    ("multiplicative mu_n", mu_n(n, p))]:
        cls = class_fiber(L, w, c, p)
        mline = max((M_line_genuine(s, c, p) for s in cls.values()), default=0)
        mfix = max((M_fixed_genuine(s, c, p) for s in cls.values()), default=0)
        # also report the largest class size (the PTE-family size)
        biggest = max((len(s) for s in cls.values()), default=0)
        print(f"  {name:>22}:  M_line={mline}  M_fixed={mfix}  ceil={ceil}  "
              f"max_class={biggest}  (line>ceil:{mline>ceil}, fixed>ceil:{mfix>ceil})")

# ---------------------------------------------------------------------------
# GAP C : the fixed-syndrome list scaling -- does M_fixed grow (weld to wall)
#         or stay O(1) (rank form usable)?  on BOTH domains.
# ---------------------------------------------------------------------------

def expC_fixed_scaling(w, c, additive_Ns, mun_ns):
    banner(f"GAP C  M_fixed (intended fixed-syndrome list) SCALING   w={w} c={c}")
    D = w + c
    ceil = (2 * D - 1) // c
    print(f"  ceiling floor((2D-1)/c)={ceil} (CONSTANT in n).  Does M_fixed grow?")
    print("  -- additive {0..N-1}:")
    for N in additive_Ns:
        L = list(range(N))
        p = prize_prime(N)
        cls = class_fiber(L, w, c, p)
        mfix = max((M_fixed_genuine(s, c, p) for s in cls.values()), default=0)
        print(f"      N={N:>3}  M_fixed={mfix:>3}  (>ceil:{mfix>ceil})")
    print("  -- multiplicative mu_n:")
    for n in mun_ns:
        if n < w:
            continue
        p = prize_prime(n)
        L = mu_n(n, p)
        cls = class_fiber(L, w, c, p)
        mfix = max((M_fixed_genuine(s, c, p) for s in cls.values()), default=0)
        print(f"      n={n:>3}  M_fixed={mfix:>3}  (>ceil:{mfix>ceil})")

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("wf407 / T232-11-conj41 -- which printed form of Conjecture 41 is INTENDED,")
    print("and does it survive (usable list bound) or weld onto the PTE/esymm wall?\n")

    # GAP A: the refuted count-over-line vs the intended fixed-syndrome list (additive).
    expA_line_vs_fixed([8, 10, 11, 12, 13, 14, 15, 16], w=6, c=3)
    expA_line_vs_fixed([10, 12, 14, 16], w=5, c=4)

    # GAP B: the prize MULTIPLICATIVE domain mu_n.
    expB_mun_domain([8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24], w=6, c=3)
    expB_mun_vs_additive(14, w=6, c=3)
    expB_mun_vs_additive(16, w=6, c=3)
    expB_mun_vs_additive(20, w=6, c=3)

    # GAP C: does the INTENDED (fixed-syndrome) list grow or stay O(1)?
    expC_fixed_scaling(w=6, c=3,
                       additive_Ns=[10, 12, 14, 16, 18, 20],
                       mun_ns=[8, 12, 16, 20, 24, 28, 32])

    print("\nDONE.")
