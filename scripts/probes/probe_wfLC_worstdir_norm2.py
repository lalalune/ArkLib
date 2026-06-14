#!/usr/bin/env python3
"""
LANE LC (#407) — EXACT max-excess-prime for the WORST direction, FAST integer route.

Same object as probe_wfLC_worstdir_norm.py (validated: reproduced 8161=n^3.249 exactly) but the
norm is computed as an INTEGER resultant:  represent h_{b-k}(zeta_n^T) as an integer polynomial
P(x) of degree < n (reduce all exponents mod n; over Z[zeta_n] the value lies in the power basis),
then  N = Res_x( Phi_n(x), P(x) )  is the exact rational norm (an integer).  One integer resultant
per subset => fast, exact (no floats).

beta_excess(n) = log_n(max prime factor over w-subsets with N != 0).
  <4  => worst dir FAITHFUL at the prize prime (beta=4); >=4 => prize prime saturates (REFUTES).
"""
import sys, itertools, math
sys.path.insert(0, 'scripts/probes')
import sympy
from sympy import symbols, Poly, cyclotomic_poly, resultant
from itertools import combinations_with_replacement

x = symbols('x')

def h_coeffs_mod_n(deg, T, n):
    """coefficient vector (len n) of h_deg(zeta^T) reduced via zeta^n=1 (exponents mod n)."""
    c = [0]*n
    for combo in combinations_with_replacement(T, deg):
        e = sum(combo) % n
        c[e] += 1
    return c

def exact_norm(deg, T, n, Phi):
    c = h_coeffs_mod_n(deg, T, n)
    if not any(c): return 0
    P = Poly({ (e,): c[e] for e in range(n) if c[e] }, x)
    if P.is_zero: return 0
    return int(resultant(Phi.as_expr(), P.as_expr(), x))

def beta_excess(n, k, a, b, w):
    deg = b - k
    Phi = Poly(cyclotomic_poly(n, x), x)
    maxp = 1; nzero = 0; nt = 0; worstT = None
    for T in itertools.combinations(range(n), w):
        N = exact_norm(deg, T, n, Phi)
        if N == 0: nzero += 1; continue
        nt += 1
        if abs(N) == 1: continue
        f = sympy.factorint(abs(N))
        m = max(f.keys())
        if m > maxp: maxp = m; worstT = T
    be = math.log(maxp)/math.log(n) if maxp>1 else 0.0
    return be, maxp, nzero, nt, worstT

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--configs', default='val')
    args = ap.parse_args()
    print("="*84)
    print("LANE LC EXACT max-excess-prime, WORST direction (integer resultant norm)")
    print("  beta_excess<4 => worst dir FAITHFUL at prize | >=4 => prize prime saturates (refute)")
    print("="*84)
    if args.configs == 'val':
        CFG = [
            (16,4,7,7,5,  "n=16 h_3 deg3 w=5 [VALIDATE vs 8161=n^3.25]"),
            (16,4,4,10,5, "n=16 WORST dir(4,10) deg6 w=5"),
            (16,4,4,10,6, "n=16 WORST dir(4,10) deg6 w=6"),
            (16,4,4,10,7, "n=16 WORST dir(4,10) deg6 w=7"),
        ]
    else:  # n=32 apex: h_3 readout (deg3) + worst dir, feasible w bands
        CFG = [
            (32,8,11,11,5, "n=32 h_3 deg3 w=5"),
            (32,8,11,11,6, "n=32 h_3 deg3 w=6"),
            (32,8,11,11,7, "n=32 h_3 deg3 w=7"),
            (32,8,8,20,5,  "n=32 WORST dir(8,20) deg12 w=5"),
            (32,8,8,20,6,  "n=32 WORST dir(8,20) deg12 w=6"),
            (32,8,8,20,7,  "n=32 WORST dir(8,20) deg12 w=7"),
        ]
    for (n,k,a,b,w,lab) in CFG:
        be,mpx,nz,nt,wT = beta_excess(n,k,a,b,w)
        side = "FAITHFUL@prize" if be<4 else "EXCESS reaches prize"
        print(f"  {lab}: deg={b-k} w={w} nonzero={nt} char0_zero={nz} "
              f"max_excess_prime={mpx} beta_excess={be:.3f} [{side}] worstT={wT}", flush=True)
