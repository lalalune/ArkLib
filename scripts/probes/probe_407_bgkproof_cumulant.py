#!/usr/bin/env python3
"""
#407 STRATEGY 4 — CUMULANT decay attack on the Dyadic Sub-Gaussian Energy Lemma.

TARGET (assume true, find a PROOF):  A_r := (1/p) sum_{b!=0} |eta_b|^{2r}
       = E_r(mu_n) - n^{2r}/p   <=   Wick := (2r-1)!! * n^r   for all r <= ~log p.
  eta_b = sum_{x in mu_n} e_p(b x),  n = 2^mu,  p == 1 mod n.

CUMULANT FRAMING.  Treat the (p-1) complex numbers {eta_b : b != 0} as a "sample"
weighted by 1/p.  Then:
  - the 2nd moment is exactly  m_2 := (1/p) sum_{b!=0}|eta_b|^2 = n - n^2/p  (Parseval, verified).
  - Wick = (2r-1)!! n^r is the 2r-th moment of a complex Gaussian with variance n
    (E|Z|^{2r}=r! n^r for circular complex Gaussian; (2r-1)!! n^r is the REAL-Gaussian
    2r-th moment with variance n).  KEY: eta_b is REAL here (4|n => mu_n negation-closed =>
    eta_b real), so the right Gaussian comparison is the REAL one and Wick=(2r-1)!! n^r is
    exactly the 2r-th moment of N(0,n).  Verified below.

  So  A_r <= Wick  <==>  the 2r-th moment of {eta_b} is <= that of a Gaussian N(0,n).
  Sub-Gaussianity <==> all CUMULANTS kappa_{2j} of {eta_b} for j>=2 are <= 0 (or controlled).

DELIVERABLES of this probe:
  (D1) Verify eta_b real, m_2 = n - n^2/p exactly, Wick = real-Gaussian moment.
  (D2) Compute the cumulants kappa_{2j} of {eta_b} (1/p weighted) EXACTLY via the
       moment-cumulant (Bell) recursion.  SIGN and SCALE.  Is kappa_4 <= 0 ?
  (D3) Express kappa_{2j} as a CONNECTED additive-energy count (the "connected anomaly").
       Check kappa identity:  the connected char-p relation count.
  (D4) Decompose into char-0 connected + char-p connected.  Char-0 connected cumulant of a
       Lam-Leung (pure-pair) ensemble: should VANISH for j>=2 in the n->infty limit (Gaussian),
       be slightly NEGATIVE for finite n (the (2r-1)!! is an UPPER bound on the ring count R_r).
       Char-p connected = the anomaly.  Measure both signs/scales.
"""
import math
import numpy as np
from sympy import primerange
from math import comb

def doublefact(r):
    d = 1.0
    for j in range(1, 2*r, 2):
        d *= j
    return d

def setup_mu(n, p):
    """Return mu_n as a list of residues, with zeta of order n, zeta^{n/2} = -1."""
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            return [pow(z, j, p) for j in range(n)]
    raise RuntimeError("no zeta")

def eta_all(n, p):
    """eta_b for all b in 0..p-1 via FFT of the indicator of mu_n.  Returns complex array."""
    mu = setup_mu(n, p)
    ind = np.zeros(p)
    for x in mu:
        ind[x] = 1.0
    F = np.fft.fft(ind)        # F[b] = sum_x e^{-2pi i b x / p}
    return np.conj(F)          # eta_b = sum_x e^{+2pi i b x / p}

def raw_moments(eta, p, rmax):
    """m_{2r} := (1/p) sum_{b != 0} |eta_b|^{2r}  for r=0..rmax.  (b=0 excluded.)"""
    e2 = np.abs(eta)**2
    e2[0] = 0.0  # drop DC; we sum over b != 0
    out = []
    for r in range(rmax+1):
        out.append(float((e2**r).sum()) / p if r >= 1 else float((eta != 0).sum())/p)
    # r=0 term is just (p-1)/p of mass; but for moment-cumulant we treat measure with total mass.
    return out

def cumulants_from_central_moments(mu_even, var):
    """
    Given EVEN central moments mu_2=var, mu_4, mu_6, ... (odd ones 0 for symmetric real dist),
    compute cumulants kappa_2, kappa_4, ... via the standard recursion
        mu_n = sum_{k=0}^{n-1} C(n-1,k) kappa_{n-k} mu_k   (mu_0=1).
    We use the moment-cumulant relation for a SYMMETRIC real distribution.
    mu_even is dict: {2:..., 4:..., 6:...}.  Returns dict kappa {2:...,4:...,...}.
    """
    # Build full moment list mu[0..N] (odd = 0).
    maxord = max(mu_even.keys())
    mu = [0.0]*(maxord+1)
    mu[0] = 1.0
    for k, v in mu_even.items():
        mu[k] = v
    kappa = [0.0]*(maxord+1)
    # recursion: mu_n = sum_{k=0}^{n-1} C(n-1,k) kappa_{n-k} mu_k
    for nord in range(1, maxord+1):
        s = 0.0
        for k in range(0, nord):
            s += comb(nord-1, k) * kappa[nord-k] * mu[k] if (nord-k) != nord else 0.0
        # the k=0 term has kappa_n * mu_0 = kappa_n; solve:
        # mu_n = kappa_n + sum_{k=1}^{n-1} C(n-1,k) kappa_{n-k} mu_k
        rest = 0.0
        for k in range(1, nord):
            rest += comb(nord-1, k) * kappa[nord-k] * mu[k]
        kappa[nord] = mu[nord] - rest
    return {j: kappa[j] for j in range(2, maxord+1, 2)}

def main():
    print("="*100)
    print("STRATEGY 4 — CUMULANT structure of {eta_b : b != 0} (1/p weighted)")
    print("Target: A_r <= Wick=(2r-1)!! n^r  <==>  cumulants kappa_{2j}(j>=2) <= 0 (sub-Gaussian)")
    print("="*100)

    for n, beta in [(8,4),(16,4),(32,4),(64,4)]:
        p = next(q for q in primerange(int(n**beta), int(n**beta*3)) if q % n == 1)
        eta = eta_all(n, p)
        # (D1) eta real?
        maximag = float(np.abs(eta.imag).max())
        rmax = 6
        m = raw_moments(eta, p, rmax)
        # central moments of the REAL variable eta_b (mean ~ 0): mu_{2r} = (1/p) sum_{b!=0} eta_b^{2r}
        # since eta real, |eta|^{2r} = eta^{2r}.  mean of eta over b!=0:
        mean_eta = float(eta.real[1:].sum())/p
        var = m[1]                      # m_2 = (1/p) sum eta^2  (~ n - n^2/p)
        print(f"\nn={n:3d} p={p} (beta={beta}) : max|Im eta|={maximag:.2e}  mean_eta={mean_eta:+.4f}  "
              f"m_2={var:.4f}  n - n^2/p={n - n*n/p:.4f}")
        mu_even = {2*r: m[r] for r in range(1, rmax+1)}
        kappa = cumulants_from_central_moments(mu_even, var)
        print(f"     Wick(real-Gauss N(0,n)) moments vs measured, and cumulants:")
        print(f"       {'r':>2} {'A_r=m_{2r}':>14} {'Wick=(2r-1)!!n^r':>18} {'A_r/Wick':>9} "
              f"{'kappa_{2r}':>14} {'kappa/n^r':>10}")
        for r in range(1, rmax+1):
            W = doublefact(r)*n**r
            kap = kappa.get(2*r, float('nan'))
            print(f"       {r:>2} {m[r]:>14.2f} {W:>18.2f} {m[r]/W:>9.4f} {kap:>14.4f} "
                  f"{kap/n**r:>10.4f}")
    print("\n" + "="*100)
    print("READ:  A_r/Wick <= 1 (decreasing) ==> sub-Gaussian.  kappa_{2r} for r>=2 SIGN tells")
    print("whether {eta_b} is genuinely sub-Gaussian (kappa<=0) or just below Wick numerically.")
    print("="*100)

if __name__ == "__main__":
    main()
