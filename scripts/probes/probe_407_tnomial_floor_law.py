#!/usr/bin/env python3
"""
t-nomial floor on mu_n (n=2^mu). TWO engines:

ENGINE A (family, bounded d<=16): g(X)=prod_{a in A}(X^{n/d}-omega_d^a),
  d=2^{t-1}. roots=|A|*(n/d). support=#nonzero elem-symm of omega^A.
  For each t, max roots over genuine-t-support A.

ENGINE B (GROUND TRUTH, exact, all 2-power factorizations): the REAL max # of
  mu_n-roots of ANY t-sparse polynomial. A poly p with support on exponents
  E (|E|=t) vanishing on a subset S of mu_n. Over char-0, p|_{mu_n}=0 on s points
  means p shares s roots with X^n-1. Max #common-roots with X^n-1 of a t-sparse p:
  p must be divisible by prod of cyclotomic factors. We enumerate which products of
  Phi_{2^j}|(X^n-1) [the only divisors, since n=2^mu] can be a SUBPRODUCT whose
  product is t-sparse. The roots of X^n-1 split into the 2^mu = sum phi(2^j) classes.
  A t-sparse divisor's roots = union of some Phi_{2^j} root-sets (a divisor must be a
  product of full cyclotomic polys Phi_{2^j}, j<=mu). #roots = sum of chosen phi(2^j).
  We then need the PRODUCT of chosen Phi_{2^j} to be t-sparse (support t).
"""
import numpy as np
from itertools import combinations
import sympy as sp


def support_size(coeffs):
    return int(np.sum(np.abs(np.array(coeffs)) > 1e-9))


def engine_A(mu):
    n = 2 ** mu
    out = {}
    for t in range(2, mu + 1):
        d = 2 ** (t - 1)
        if d > 16:  # bounded
            out[t] = None
            continue
        best = None
        for r in range(1, d + 1):
            for A in combinations(range(d), r):
                roots = [np.exp(2j * np.pi * a / d) for a in A]
                supp = support_size(np.poly(roots))
                if supp == t:
                    rc = len(A) * (n // d)
                    if best is None or rc > best[0]:
                        best = (rc, list(A))
        out[t] = best
    return n, out


def engine_B(mu):
    """Ground truth via cyclotomic divisors of X^n-1, n=2^mu.
    Divisors of X^{2^mu}-1 = prod_{j=0}^{mu} Phi_{2^j}.
    Phi_1=X-1, Phi_2=X+1, Phi_{2^j}=X^{2^{j-1}}+1 for j>=1.
    deg Phi_{2^j} = phi(2^j) = 2^{j-1} (j>=1), and 1 for j=0.
    A divisor D = prod over a chosen subset J of {0..mu} of Phi_{2^j}.
    #roots(D in mu_n) = sum_{j in J} deg Phi_{2^j}.
    support(D) = #nonzero coeffs of the product. Find max #roots with support==t.
    """
    X = sp.symbols('X')
    phis = {}
    for j in range(mu + 1):
        phis[j] = sp.cyclotomic_poly(2 ** j, X)
    results = {}  # t -> max roots
    bestwitness = {}
    for r in range(1, mu + 2):
        for J in combinations(range(mu + 1), r):
            D = sp.Integer(1)
            for j in J:
                D = sp.expand(D * phis[j])
            poly = sp.Poly(D, X)
            supp = len([c for c in poly.all_coeffs() if c != 0])
            nroots = sum(sp.totient(2 ** j) if j >= 1 else 1 for j in J)
            # totient(1)=1 ok; for j=0 phi=1
            if supp not in results or nroots > results[supp]:
                results[supp] = nroots
                bestwitness[supp] = J
    return results, bestwitness


print("=" * 72)
print("ENGINE A: factor-through-order-2^{t-1} family (bounded d<=16)")
print("=" * 72)
for mu in range(3, 8):
    n, out = engine_A(mu)
    line = "n=%4d:" % n
    for t in sorted(out):
        b = out[t]
        if b:
            line += "  t%d->%d" % (t, b[0])
        else:
            line += "  t%d->(skip)" % t
    print(line)
    # predicted floor law (t-1)*n/2^{t-1}
    pred = "        pred (t-1)*n/2^(t-1):"
    for t in range(2, mu + 1):
        pred += "  t%d->%d" % (t, (t - 1) * n // (2 ** (t - 1)))
    print(pred)

print()
print("=" * 72)
print("ENGINE B: GROUND-TRUTH max mu_n-roots of ANY t-sparse 2-power divisor")
print("(support t -> max #roots, with cyclotomic factor subset)")
print("=" * 72)
for mu in range(3, 8):
    n = 2 ** mu
    results, wit = engine_B(mu)
    print("\n--- n=%d (mu=%d) ---" % (n, mu))
    for supp in sorted(results):
        J = wit[supp]
        facs = "*".join("Phi_%d" % (2 ** j) for j in J)
        print("  support=%2d: max_roots=%3d  (=n/%s)  via %s" %
              (supp, results[supp],
               (str(n // results[supp]) if n % results[supp] == 0 else "%.2f" % (n / results[supp])),
               facs))
