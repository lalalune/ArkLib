#!/usr/bin/env python3
"""
#407 C5 — telescoped-closure growth, FFT-accelerated (deep towers at large 2-adic primes).

eta_b(mu_n) = sum_{x in mu_n} e_p(b x) = sum_{r=0}^{p-1} 1_{mu_n}(r) * exp(2pi i b r/p)
            = conj( DFT of indicator )_b   (up to sign convention). Compute ALL b via one FFT.

Confirms: the only telescoping closure (Young: A_k(n)<=4^k A_k(n/2)) gives n^{2k} (trivial/Johnson)
growth, while Wick needs n^k. The PER-LEVEL true ratio A_k(2^mu)/A_k(2^{mu-1}) sits strictly
between 2^k (Wick-needed) and 4^k (Young-allowed) -- the recursion cannot push it to 2^k. This is
the moment-version of the L^infty 'M(n)^2 vs 2 M(n/2)^2' alignment obstruction.
"""
import numpy as np
from sympy import primitive_root as pr

def gauss_periods(n, p):
    """return array eta[b]=sum_{x in mu_n} e_p(b x), b=0..p-1 (real for 4|n)."""
    g=int(pr(p)); t=pow(g,(p-1)//n,p)
    ind=np.zeros(p)
    x=1
    for _ in range(n):
        ind[x]+=1.0; x=(x*t)%p
    # eta[b] = sum_r ind[r] exp(2pi i b r /p) = (IFFT-like). Use FFT: F[b]=sum_r ind[r] exp(-2pi i b r/p)
    F=np.fft.fft(ind)             # F[b]=sum_r ind[r] e^{-2pi i b r/p}
    eta=np.conjugate(F)           # = sum_r ind[r] e^{+2pi i b r/p}
    return eta

def df(m):
    r=1
    for j in range(1,m+1,2): r*=j
    return r

def Ak_all(n,p,kmax):
    eta=gauss_periods(n,p)
    mag2=np.abs(eta)**2
    mag2[0]=0.0  # drop b=0
    a=[0.0]*(kmax+1)
    pw=np.ones(p)
    for k in range(1,kmax+1):
        pw=pw*mag2
        a[k]=pw.sum()/p
    return a

def main():
    kmax=4
    for p in [40961, 65537, 786433]:
        v2=0; m=p-1
        while m%2==0: m//=2; v2+=1
        mu_max=min(v2,10)
        print(f"\n{'='*104}\np={p} (v2={v2}); per-level ratio A_k(2^mu)/A_k(2^(mu-1)) -- need 2^k (Wick), Young allows 4^k")
        prev=None
        for mu in range(1,mu_max+1):
            n=2**mu; a=Ak_all(n,p,kmax)
            if prev is not None:
                ratios=[a[k]/prev[k] if prev[k] else float('nan') for k in range(1,kmax+1)]
                print(f"  mu={mu:2d} n={n:5d}: ratio_k="+" ".join(f"{ratios[k-1]:5.2f}" for k in range(1,kmax+1))
                      +f"   (need 2^k={[2**k for k in range(1,kmax+1)]}, max 4^k={[4**k for k in range(1,kmax+1)]})")
            prev=a
        n=2**mu_max; a=Ak_all(n,p,kmax)
        print("  FINAL n=%d:"%n, " ".join(
            f"k{k}:A/Wick={a[k]/(df(2*k-1)*n**k):.3f},A/(n^2k/4^k)={a[k]/((n**(2.0*k))/4**k):.4f}"
            for k in range(1,kmax+1)))

if __name__=="__main__":
    main()
