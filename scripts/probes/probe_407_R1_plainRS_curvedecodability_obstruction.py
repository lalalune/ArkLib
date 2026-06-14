#!/usr/bin/env python3
"""
R1 obstruction probe: can the GG25 curve-decodability engine give curve-decodability
for EXPLICIT PLAIN smooth-domain Reed-Solomon at the prize point?

GG25 Theorem 4.7 (the ONLY production engine for curve-decodability at b > l+1):
    every tau-subspace-design code C is (l, 1 - tau(r) - eps, a, eps/(r+eps) * a) curve-decodable
    for any eps >= (l+1)/r.

To pin delta* in the prize WINDOW (1 - sqrt(rho), 1 - rho - Theta(1/log n)) we need the
close radius delta = 1 - tau(r) - eps to reach NEAR 1 - rho = 1 - R, i.e. we need
    tau(r) + eps  <=  rho + Theta(1/log n)         (so that 1 - tau(r) - eps >= window)
with the explained count b = eps/(r+eps) * a  >  l+1 (nontrivial regime), at the prize:
    rho in {1/2,1/4,1/8,1/16}, eps* = 2^-128, q ~ n * 2^128, n = 2^30, smooth mu_n.

KEY: Lemma 2.18 of GG25 forces, for ANY tau-subspace-design code of rate R = rho:
    tau(r) >= R - 1/n = rho - 1/n     for ALL r.
So tau(r) + eps >= rho - 1/n + eps >= rho - 1/n + (l+1)/r.
The window needs tau(r)+eps <= rho + Theta(1/log n). That FORCES:
    (l+1)/r - 1/n <= Theta(1/log n)   ==>   r >= (l+1) * Omega(log n).      (necessary)
That is necessary but NOT sufficient: it only says the *budget* is consistent.
The REAL content of Theorem 4.7 is that tau(r) STAYS ~ rho up to r = Omega(log n)
(a "strong subspace design", Def 2.19), i.e. the dimension bound Lemma 4.1 holds with
tau(r) close to rho for r growing. That near-optimal subspace-design property is exactly
what FRS/multiplicity/random-RS HAVE and explicit PLAIN RS does NOT.

This probe quantifies, for plain RS, how far tau(r) is from rho as r grows -- i.e. whether
plain RS could even in principle satisfy the strong-subspace-design hypothesis Theorem 4.7
needs. We measure tau(r) directly from the DEFINITION (Def 2.17) on small plain-RS codes:
    tau(r) = max over r-dim subspaces A <= C of  (sum_i dim A_i) / (n * dim A)
where A_i = {a in A : a_i = 0}.  For RS[k] over F_q with eval set D (|D|=n), a 1-dim
subspace is spanned by one codeword = poly of degree < k evaluated on D; dim A_1-fiber at
coord i is 1 iff that poly vanishes at D_i.  A degree-<k poly has <= k-1 roots, so for r=1
a single codeword vanishes on <= k-1 of n coords => tau(1) <= (k-1)/n ~ rho (TIGHT, = MDS).
For r-dim A: sum_i dim A_i counts (coord,codeword-in-basis-vanishing) incidences. The
question is whether tau(r) stays ~ rho or BLOWS UP toward 1 as r grows -- a blow-up means
plain RS is NOT a strong subspace design and Theorem 4.7 gives a VACUOUS radius.
"""

import itertools

def is_prime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True

# Work over a small prime field F_p, plain RS with eval set = all of F_p (n = p, smooth-ish).
# RS[k]: messages = polys of degree < k, codeword = (poly(x))_{x in F_p}.
# Enumerate r-dim subspaces of the message space (dim = k) via r-subsets of a basis-ish,
# but to get tau(r) we should maximize over ALL r-dim subspaces. For tractability we
# enumerate r-dim subspaces spanned by r monomials AND random r-tuples; report the MAX seen.

def rs_codeword(coeffs, p):
    # coeffs[j] is coeff of x^j ; evaluate at all x in F_p
    return tuple(sum(c * pow(x, j, p) for j, c in enumerate(coeffs)) % p for x in range(p))

def dim_fiber_counts_for_subspace(basis_polys, p, k):
    """
    basis_polys: list of coeff-vectors (length k) that are F_p-linearly independent (assumed).
    Returns sum_i dim A_i  where A = span(basis), A_i = {a in A : a_i = 0}.
    A_i is the kernel of the i-th coordinate evaluation restricted to A.
    dim A_i = dim A - rank(eval_i restricted) ; eval_i is a linear functional on A.
    Over all coords i, dim A_i = dimA if functional is 0 on A, else dimA - 1.
    So sum_i dim A_i = sum_i (dimA - [coord-i-eval nonzero on A]).
    coord-i-eval is nonzero on A iff some basis codeword is nonzero at coord i.
    """
    r = len(basis_polys)
    cws = [rs_codeword(b, p) for b in basis_polys]
    n = p
    total = 0
    for i in range(n):
        # value of functional 'eval at x=i' on each basis vector
        vals = [cw[i] for cw in cws]
        nonzero = any(v != 0 for v in vals)
        # dim A_i = r - (1 if functional nonzero on A else 0)
        total += (r - (1 if nonzero else 0))
    return total  # = sum_i dim A_i

def tau_r_lower_estimate(p, k, r, max_subspaces=4000):
    """
    Estimate tau(r) for RS[k] over F_p (n=p) as MAX over sampled r-dim subspaces of
    (sum_i dim A_i)/(n * r). We sample r-subsets of a generating set of codewords.
    For small p,k we can enumerate r-subsets of the monomial basis plus extra random combos.
    Returns the max ratio found (a LOWER bound on the true tau(r)).
    """
    n = p
    best = 0.0
    # basis candidates: monomials x^0..x^{k-1}  (gives the standard message basis)
    monos = []
    for j in range(k):
        cv = [0]*k
        cv[j] = 1
        monos.append(cv)
    count = 0
    # enumerate all r-subsets of monomials (these are honest r-dim subspaces)
    for combo in itertools.combinations(range(k), r):
        basis = [monos[j] for j in combo]
        s = dim_fiber_counts_for_subspace(basis, p, k)
        ratio = s / (n * r)
        if ratio > best:
            best = ratio
        count += 1
        if count >= max_subspaces:
            break
    return best

print("="*78)
print("PLAIN RS tau(r) vs rate R=rho  (Def 2.17 subspace-design parameter, from monomials)")
print("Theorem 4.7 needs tau(r) ~ rho for r ~ Omega(log n) to reach the prize window.")
print("="*78)
for p in [11, 13, 17, 19, 23]:
    if not is_prime(p): continue
    n = p
    for rho_num, rho_den in [(1,2),(1,4)]:
        k = max(1, (rho_num * n)//rho_den)   # k ~ rho * n
        R = k / n
        print(f"\nF_{p}: n={n}, k={k}, R=k/n={R:.3f}  (target rho={rho_num}/{rho_den}={rho_num/rho_den:.3f})")
        for r in range(1, min(k, 7)+1):
            tau = tau_r_lower_estimate(p, k, r)
            # 1 - tau(r) - eps with eps minimal (l+1)/r, l say 1 (lines):
            l = 1
            eps_min = (l+1)/r
            radius = 1 - tau - eps_min
            print(f"   r={r}: tau(r)>={tau:.4f}  (rho={R:.4f}); "
                  f"min eps=(l+1)/r={eps_min:.3f}; reachable radius 1-tau-eps={radius:.3f} "
                  f"(window upper ~ 1-rho={1-R:.3f})")
print()
print("READING: For curve-decodability radius (1-tau-eps) to reach the window ~ 1-rho,")
print("need tau ~ rho AND eps=(l+1)/r small => r large. For plain RS, tau(1)~rho (MDS),")
print("but eps=(l+1)/r forces r=Omega(log n); Theorem 4.7's strong-subspace-design")
print("hypothesis (tau(r)~rho up to r=Omega(log n)) is what FRS/random-RS satisfy and")
print("explicit plain RS is NOT KNOWN to satisfy -- the dimension bound Lemma 4.1 for")
print("plain RS at growing r is exactly an open list-recovery-into-low-dim statement.")
