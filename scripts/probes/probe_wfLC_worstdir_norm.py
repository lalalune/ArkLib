#!/usr/bin/env python3
"""
LANE LC (#407) — EXACT max excess prime for the WORST direction, via integer field norms.

For worst dir(a,b), readout h_{b-k}.  Char-p saturation (= char-p EXCESS over char-0) on a w-subset
T  <=>  p | N_{Q(zeta_n)/Q}( h_{b-k}(zeta_n^T) ), with the value != 0 over ℂ.

  beta_excess(n) = log_n( max prime factor over all w-subsets T with N(T) != 0 ).
  beta_excess < beta=4  =>  NO prize-scale prime saturates the worst dir  =>  FAITHFUL at prize.
  beta_excess >= 4      =>  a prize prime saturates  =>  char-p EXCESS  =>  delta* < edge.

EXACT integer norm: N = round( prod_{j: gcd(j,n)=1} h(zeta_n^j) ) at high mpmath precision (the
product over Galois conjugates IS the rational norm = an integer).  Verified-exact by integrality
check (|N - round(N)| tiny).  Fast: one product per subset (deg(Phi_n)=n/2 factors), then factor.
"""
import sys, itertools, math
sys.path.insert(0, 'scripts/probes')
import sympy
from itertools import combinations_with_replacement
import mpmath as mp
mp.mp.dps = 60

def conj_indices(n):
    return [j for j in range(1, n+1) if math.gcd(j, n) == 1]

def h_at(deg, T, zpow):
    """h_deg evaluated at {zpow[t] : t in T}, zpow[t] a complex number = zeta^t."""
    xs = [zpow[t] for t in T]
    s = mp.mpc(0)
    for combo in combinations_with_replacement(range(len(xs)), deg):
        t = mp.mpc(1)
        for c in combo: t *= xs[c]
        s += t
    return s

def exact_norm(deg, T, n, conj):
    prod = mp.mpc(1)
    for j in conj:
        zpow = [mp.e**(2j*mp.pi*(t*j)/n) for t in range(n)]
        prod *= h_at(deg, T, zpow)
    val = mp.re(prod)
    N = mp.nint(val)
    err = abs(val - N)
    return int(N), float(err)

def beta_excess(n, k, a, b, w, verbose=False):
    deg = b - k
    conj = conj_indices(n)
    maxp = 1; nzero = 0; nt = 0; maxerr = 0.0; worstT = None
    for T in itertools.combinations(range(n), w):
        N, err = exact_norm(deg, T, n, conj)
        maxerr = max(maxerr, err)
        if N == 0:
            nzero += 1; continue
        nt += 1
        if abs(N) == 1: continue
        f = sympy.factorint(abs(N))
        mp_ = max(f.keys())
        if mp_ > maxp: maxp = mp_; worstT = T
    be = math.log(maxp)/math.log(n) if maxp > 1 else 0.0
    return be, maxp, nzero, nt, maxerr, worstT

if __name__ == '__main__':
    print("="*84)
    print("LANE LC EXACT max-excess-prime for WORST direction (integer field norms, mpmath dps=60)")
    print("  beta_excess<4 => worst dir FAITHFUL at prize  |  >=4 => prize prime saturates (refute)")
    print("="*84)
    for (n,k,a,b,w,lab) in [
        (16,4,7,7,5,  "n=16 h_3 readout deg3 w=5 [CHECK vs known 8161=n^3.25]"),
        (16,4,4,10,5, "n=16 WORST dir(4,10) deg6 w=5"),
        (16,4,4,10,6, "n=16 WORST dir(4,10) deg6 w=6"),
        (16,4,4,10,7, "n=16 WORST dir(4,10) deg6 w=7"),
    ]:
        be,mpx,nz,nt,me,wT = beta_excess(n,k,a,b,w)
        side = "FAITHFUL@prize(beta=4)" if be<4 else "EXCESS reaches prize"
        print(f"  {lab}:\n     deg={b-k} w={w} nonzero_subsets={nt} char0_zero={nz} "
              f"max_excess_prime={mpx} beta_excess={be:.3f} [{side}] (norm_round_err={me:.1e}) worstT={wT}",
              flush=True)
