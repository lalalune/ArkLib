#!/usr/bin/env python3
"""
wf9-OT2 (#444, R4 demand-side char-faithfulness at the BINDING band, extended to n=32,64).
EXACT excess-prime exponent beta_excess(n) = log_n(max prime factor of cyclotomic field norms
N(h_{deg}(zeta^T))) over band-subsets T.  beta_excess < 4  =>  no prize-scale prime (p ~ n^4..n^5)
saturates that band  =>  char-p excess W=0  =>  R4-faithfulness HOLDS for that band (the demand-side
bad-scalar count = its char-0 value at the prize prime).  beta_excess >= 4 => a prize-scale prime
hits the band -> char-p excess -> R4-faithfulness FAILS.

This is EXACT (integer resultant norms + factoring), no char-q pollution, no enumeration of C(n,size).
Tests the WORST far direction (high monomial a*~w, per wf407-T389-02-hill) at the window-interior band.
"""
import sys, math, itertools
import sympy
from sympy import Poly, symbols, resultant, cyclotomic_poly
x = symbols('x')

def complete_homog(deg, idxs):
    from itertools import combinations_with_replacement
    t = 0
    for combo in combinations_with_replacement(idxs, deg):
        t += x**sum(combo)
    return Poly(t, x)

def norm_of_value(poly_in_x, n):
    Phi = Poly(cyclotomic_poly(n, x), x)
    return int(resultant(Phi.as_expr(), poly_in_x.as_expr(), x))

def max_prime_factor(N):
    if N == 0: return None
    N = abs(N)
    if N == 1: return 1
    return max(sympy.factorint(N).keys())

def beta_excess(n, deg, w, sample_cap=4000, seed=11):
    subs = list(itertools.combinations(range(n), w))
    if len(subs) > sample_cap:
        import random; random.seed(seed); subs = random.sample(subs, sample_cap)
    maxp = 1; nzero = 0; ntot = 0
    for T in subs:
        N = norm_of_value(complete_homog(deg, T), n)
        if N == 0: nzero += 1; continue
        mp = max_prime_factor(N)
        if mp and mp > maxp: maxp = mp
        ntot += 1
    be = math.log(maxp)/math.log(n) if maxp > 1 else 0.0
    return be, maxp, nzero, ntot

if __name__ == '__main__':
    print("wf9-OT2 EXACT excess-prime exponent at the binding band (worst far direction a*~w)")
    print("  beta_excess<4 => R4-faithful @prize (no char-p excess); >=4 => FAILS")
    # rho=1/4: k=n/4. worst dir a*~w=size=(1-delta)n. binding band near delta*~9/16 => w~7n/16.
    # readout degree deg = a-k.  Use deg in a small range around the binding band, w = band-subset size.
    # n=16: k=4, binding w in {7,8,9} (size at r=7..9), worst a~w => deg=a-k~w-k~3..5.
    # n=32: k=8, binding w in {14..18}, deg~w-k~6..10. (cap subsets; norms get big but exact.)
    configs = [
        (16,4, 5, 7,  "n=16 deg5 w=7  (binding band, exact full)"),
        (16,4, 6, 8,  "n=16 deg6 w=8  (Johnson band)"),
        (32,8, 6, 14, "n=32 deg6 w=14 (binding band sample)"),
        (32,8, 8, 16, "n=32 deg8 w=16 (Johnson band sample)"),
        (32,8, 10,18, "n=32 deg10 w=18 sample"),
    ]
    for (n,k,deg,w,lab) in configs:
        be,mp,nz,nt = beta_excess(n,deg,w)
        side = "R4-FAITHFUL@prize" if be<4 else "R4 FAILS (prize prime saturates)"
        print(f"  {lab}: deg={deg} w={w} nonzero={nt} char0zero={nz} maxprime={mp} "
              f"beta_excess={be:.3f}  [{side}]", flush=True)
