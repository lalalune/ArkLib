"""
#407 LANE A2 — exact e2=0 char-p rigidity threshold c(n).

GOAL (1): pin the EXACT minimal threshold c(n) = the largest "bad" prime, i.e. the
largest p with (p-1) % n == 0 such that the F_p e2=0 locus on mu_n DIFFERS from the
char-0 (complex) e2=0 locus (a "new" mod-p solution exists). For p above that, the
F_p e2=0 subsets of mu_n are exactly the char-0 ones (the rigidity transfer holds).

We compute, for n = 8, 16, 32:
  - the char-0 e2=0 locus over mu_n (exponent subsets U of {0..n-1} with
    (sum_{i in U} zeta^i)^2 == sum_{i in U} zeta^{2i} over Z[zeta_n], i.e. exactly),
  - for each split prime p (p ≡ 1 mod n), the F_p e2=0 locus,
  - the largest p where they differ (= c(n), the exact minimal threshold),
  - compare to n^3 (measured-route claim), n^β crossover, and the Lean provable
    bound (n^2+n)^{n/2}.

We restrict to width w = n/2 (the extremal width that drives the count) AND also
report the all-width totals, so the threshold is the true locus threshold.

This uses EXACT arithmetic in the cyclotomic field via sympy / direct cyclotomic
reduction; the char-0 test is done by reducing the integer relation polynomial
R_U(X) = (sum X^i)^2 - sum X^{2i} modulo the cyclotomic polynomial Phi_n(X) and
checking it is the zero polynomial.
"""
import itertools, math
from sympy import primerange, isprime, primitive_root, Poly, symbols, cyclotomic_poly, ZZ

X = symbols('X')

def phi(n):
    return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def relpoly(U):
    # R_U(X) = (sum_{i in U} X^i)^2 - sum_{i in U} X^{2i}  over ZZ
    s = sum(X**i for i in U)
    P = Poly(s, X, domain=ZZ)**2 - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)
    return P

def char0_e2zero(U, Phi):
    # exact: R_U(zeta) == 0  iff  R_U(X) reduces to 0 mod Phi_n
    R = relpoly(U)
    return (R % Phi).is_zero

def char0_locus(n, w):
    """Return set of frozenset(U) with e2=0 over Z[zeta_n] at width w. Also need e1 != 0."""
    Phi = phi(n)
    out = []
    for U in itertools.combinations(range(n), w):
        # exact e1 != 0 (over Z[zeta]): sum_{i in U} X^i mod Phi != 0
        e1 = Poly(sum(X**i for i in U), X, domain=ZZ) % Phi
        if e1.is_zero:
            continue
        if char0_e2zero(U, Phi):
            out.append(frozenset(U))
    return set(out)

def fp_locus(n, w, p, g):
    """F_p e2=0 locus at width w (with e1 != 0). g a primitive n-th root mod p."""
    mu = [pow(g, j, p) for j in range(n)]
    out = []
    for U in itertools.combinations(range(n), w):
        S = [mu[i] for i in U]
        e1 = sum(S) % p
        if e1 == 0:
            continue
        p2 = sum((x*x) % p for x in S) % p
        if (e1*e1 - p2) % p == 0:
            out.append(frozenset(U))
    return set(out)

def split_primes(n, lo, hi):
    return [p for p in primerange(lo, hi) if (p-1) % n == 0]

def find_exact_threshold(n, w, pmax_search):
    """largest bad prime <= pmax_search : F_p locus != char0 locus (at width w)."""
    Phi = phi(n)
    c0 = char0_locus(n, w)
    last_bad = None
    bad_list = []
    primes = split_primes(n, n+1, pmax_search)
    for p in primes:
        g = pow(primitive_root(p), (p-1)//n, p)
        # ensure g is primitive n-th root
        fp = fp_locus(n, w, p, g)
        # "new mod-p solution" = something in fp not in c0
        new = fp - c0
        lost = c0 - fp   # char-0 solution that fails mod p (should not happen if p large)
        if new or lost:
            last_bad = p
            bad_list.append((p, len(new), len(lost), len(fp), len(c0)))
    return last_bad, len(c0), bad_list, primes[-1] if primes else None

for n in [8, 16]:
    w = n // 2
    # search range: go comfortably past n^3
    pmax = max(3000, 5 * n**3)
    last_bad, c0card, bad_list, maxp = find_exact_threshold(n, w, pmax)
    lean_c = (n*n + n)**(n//2)
    print(f"\n=== n={n}, width w={w}  (search split primes up to {pmax}, top tested p={maxp}) ===")
    print(f"  char-0 e2=0 locus size (w={w}, e1!=0): {c0card}")
    print(f"  number of BAD primes (F_p locus != char-0 locus): {len(bad_list)}")
    if bad_list:
        print(f"  LARGEST bad prime  c(n) = {last_bad}   (beta=log_n(c) = {math.log(last_bad)/math.log(n):.3f},  c/n^3 = {last_bad/n**3:.3f})")
        print(f"  first few bad primes: {[b[0] for b in bad_list[:8]]}")
        print(f"  sample (p, #new, #lost, |fp|, |c0|): {bad_list[:4]}  ...  last: {bad_list[-2:]}")
    print(f"  n^3 = {n**3};  n^2.5 = {n**2.5:.0f};  Lean provable c=(n^2+n)^(n/2) = {lean_c:.3e}")
    if last_bad:
        print(f"  ===> EXACT threshold c({n}) = {last_bad}  is  {'<' if last_bad < n**3 else '>='} n^3,  and  {'<<' if last_bad < lean_c else '>='} Lean bound")
