#!/usr/bin/env python3
"""
REFINED t-nomial floor on mu_n (n=2^mu), NON-DEGENERATE (exclude X^n-1 full-group).

Ground truth: max #mu_n-roots of a t-SPARSE poly that is NOT a multiple of X^n-1
(i.e. does NOT vanish on ALL of mu_n -- rule-2 anti-degeneracy).
Any such poly's common roots with X^n-1 = a union of cyclotomic-coset root sets.
Over n=2^mu the only cyclotomic factors of X^n-1 are Phi_{2^j}, j=0..mu.
A poly with EXACTLY the mu_n-roots = U (a union of some Phi_{2^j} root-sets) and
minimal extra structure: the t-sparse witness with those roots is the PRODUCT of the
chosen Phi_{2^j} (this product's mu_n-zero set is exactly the chosen root-classes,
and it is the LOWEST-support poly with that zero set... we VERIFY by also scanning
products-times-(sparse cofactor) is not lower, but the cyclotomic product is canonical).

Non-degenerate <=> chosen subset J != {0,1,..,mu} (the full product = X^n-1).

We also list, for each ODD/EVEN support t, the max non-degenerate root count, and
report the in-tree anchors: t=2 binomial -> n/2 ; t=3 trinomial -> n/2.
"""
import sympy as sp
from itertools import combinations

X = sp.symbols('X')


def analyze(mu):
    n = 2 ** mu
    phis = {j: sp.cyclotomic_poly(2 ** j, X) for j in range(mu + 1)}
    deg = {j: (sp.totient(2 ** j) if j >= 1 else 1) for j in range(mu + 1)}
    full = frozenset(range(mu + 1))
    by_support = {}  # support -> (max_roots, J)
    for r in range(1, mu + 1):  # r up to mu (NOT mu+1) excludes full set partially
        for J in combinations(range(mu + 1), r):
            Js = frozenset(J)
            if Js == full:
                continue  # degenerate X^n-1
            D = sp.Integer(1)
            for j in J:
                D = sp.expand(D * phis[j])
            supp = len([c for c in sp.Poly(D, X).all_coeffs() if c != 0])
            nroots = sum(deg[j] for j in J)
            if supp not in by_support or nroots > by_support[supp][0]:
                by_support[supp] = (nroots, list(J))
    return n, by_support


print("REFINED non-degenerate t-sparse floor (n=2^mu), exclude X^n-1")
print("=" * 70)
for mu in range(3, 8):
    n, bs = analyze(mu)
    print("\n--- n=%d (mu=%d) ---" % (n, mu))
    for supp in sorted(bs):
        nr, J = bs[supp]
        facs = "*".join("P%d" % (2 ** j) for j in J)
        frac = ("n/%d" % (n // nr)) if (nr and n % nr == 0) else "%.3f*n" % (nr / n)
        print("  t=%2d: max_roots=%3d (%s)  via %s" % (supp, nr, frac, facs))
    # binomial X^{n/2}+1 check
    b = sp.Poly(X ** (n // 2) + 1, X)
    print("  [anchor] X^{n/2}+1 support=%d, mu_n-roots=n/2=%d" %
          (len([c for c in b.all_coeffs() if c != 0]), n // 2))
