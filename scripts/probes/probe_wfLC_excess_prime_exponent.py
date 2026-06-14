#!/usr/bin/env python3
"""
LANE LC (#407, R4 char-faithfulness at constant rate) — EXACT excess-prime exponent.

DECISIVE KNIFE-EDGE TEST.  Char-p far-line incidence at the worst direction SATURATES (= char-p
EXCESS over char-0) on a band-subset T  <=>  the complete-homogeneous readout h_{b-k}(zeta^T)
vanishes mod p but not over ℂ  <=>  p | N(h_{b-k}(zeta^T)) (the cyclotomic field NORM, an integer).

So the set of "excess primes" for a band is EXACTLY the set of prime factors of the integers
{ N(h_{b-k}(zeta^T)) : T a band-sized subset, h_{b-k}(zeta^T) != 0 over ℂ }.

  max excess prime exponent  beta_excess(n) := log_n( max prime factor over all band-subsets ).

  CLOSURE side : beta_excess(n) < 4  for all n  =>  prize prime (beta in [4,5]) is FAITHFUL at the
                 worst direction in the binding band  =>  delta* = char-0 Kambire edge.
  REFUTE side  : beta_excess(n) >= 4 for some n  =>  a prize-scale prime saturates the worst
                 direction at that band  =>  char-p excess, delta* < Kambire edge.

This is EXACT (integer norms + factoring), not sampled — unlike the 7-sample n=64 lower bound.
Norm computed via resultant with the n-th cyclotomic polynomial (sympy), exact over ℚ.
"""
import sys, math, itertools
sys.path.insert(0, 'scripts/probes')
import sympy
from sympy import Poly, symbols, resultant, cyclotomic_poly, ZZ

x = symbols('x')

def complete_homog(deg, idxs):
    """h_{deg}(x^{i} : i in idxs) as a sympy Poly in x (each variable = x^i)."""
    from itertools import combinations_with_replacement
    terms = 0
    for combo in combinations_with_replacement(idxs, deg):
        e = sum(combo)
        terms += x**e
    return Poly(terms, x)

def norm_of_value(poly_in_x, n):
    """N_{Q(zeta_n)/Q}( poly_in_x evaluated at zeta_n ) = Res_x(Phi_n(x), poly_in_x), an integer."""
    Phi = Poly(cyclotomic_poly(n, x), x)
    r = resultant(Phi.as_expr(), poly_in_x.as_expr(), x)
    return int(r)

def max_prime_factor(N):
    if N == 0: return None
    N = abs(N)
    if N == 1: return 1
    f = sympy.factorint(N)
    return max(f.keys())

def beta_excess(n, k, a, b, w, sample_cap=None):
    """
    Worst direction dir(a,b); readout degree = b-k (complete homogeneous).
    Saturation (= char-p excess) on a w-subset T  <=>  h_{b-k}(zeta^T) = 0 mod p  (not over ℂ),
    matching the in-tree merge-only mechanism (probe_mergeonly_saturation_refute.py): T is the
    readout-argument subset of size w directly.  For each w-subset T with nonzero ℂ-norm, max
    prime factor of N(h_{b-k}(zeta^T)).  Returns (beta_excess, max_prime, n_zero, n_tot).
    """
    deg = b - k
    if deg <= 0: return None
    subs = list(itertools.combinations(range(n), w))
    if sample_cap and len(subs) > sample_cap:
        import random; random.seed(11); subs = random.sample(subs, sample_cap)
    maxp = 1; nzero = 0; ntot = 0
    for T in subs:
        poly = complete_homog(deg, T)
        N = norm_of_value(poly, n)
        if N == 0:
            nzero += 1     # vanishes over ℂ too: char-0 already saturates (not an EXCESS)
            continue
        mp = max_prime_factor(N)
        if mp and mp > maxp: maxp = mp
        ntot += 1
    be = math.log(maxp)/math.log(n) if maxp > 1 else 0.0
    return be, maxp, nzero, ntot

if __name__ == '__main__':
    print("="*80)
    print("LANE LC EXACT excess-prime exponent  beta_excess(n) = log_n(max prime factor of norms)")
    print("  beta_excess < 4 => prize prime FAITHFUL (closure side)")
    print("  beta_excess >=4 => prize-scale prime SATURATES worst dir (refute side)")
    print("="*80)
    # Worst direction dir(n/4, 5n/8); readout deg = b-k = 5n/8 - n/4 = 3n/8.  That deg is huge for
    # large n -> use the in-tree binder form too (low-exponent h_{b-k}).  Test BOTH:
    #   (i) the merge-only h_3 readout (deg 3) at the band the live session used (the feasible apex)
    #   (ii) the worst monomial dir(n/4,5n/8)
    configs = [
        # (n,k,a,b, w, label, sample_cap)   w = readout-subset size (the band)
        (16,4, 7, 7, 5,  "n=16 h_3 readout (deg3) w=5 [reproduce merge-only]", None),
        (16,4, 4, 10, 5, "n=16 worst dir(4,10) deg6 w=5", None),
        (16,4, 4, 10, 6, "n=16 worst dir(4,10) deg6 w=6", None),
        (16,4, 4, 10, 7, "n=16 worst dir(4,10) deg6 w=7", None),
    ]
    for (n,k,a,b,w,lab,cap) in configs:
        res = beta_excess(n,k,a,b,w,cap)
        if res is None: print(f"  {lab}: deg<=0 skip"); continue
        be,mp,nz,nt = res
        side = "FAITHFUL@prize" if be<4 else "EXCESS reaches prize"
        print(f"  {lab}: deg={b-k} w={w} subsets_nonzero={nt} char0_zero={nz} "
              f"max_excess_prime={mp} beta_excess={be:.3f}  [{side}]")
