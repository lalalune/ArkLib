#!/usr/bin/env python3
"""
#407 STRATEGY 2 — DERIVE the exact moment recursion and test telescoping.

Goal: relate A_r(mu_n) to level-(n/2) quantities via the parallelogram split
  eta_b(mu_n) = A_b + B_b,  A_b = eta_b(mu_{n/2}),  B_b = eta_{zeta b}(mu_{n/2}).

Define the level-(n/2) cross-moment over frequencies (the natural object):
  For the map T: b -> zeta b (multiplication by zeta, a permutation of F_p^*),
    A_b = f(b),  B_b = f(zeta b) = f(Tb),  where f(b) := eta_b(mu_{n/2}).
  So  p*A_r(mu_n) = sum_{b!=0} |f(b) + f(Tb)|^{2r}.

We expand |f(b)+f(Tb)|^{2r} and SUM over b. Key questions:
  (Q1) The "diagonal" sum_{b} |f(b)|^{2r} = p*A_r(mu_{n/2}) (level n/2).
       Also sum_b |f(Tb)|^{2r} = p*A_r(mu_{n/2}) (T permutes).
  (Q2) Cross terms sum_b f(b)^a conj(f(b))^c f(Tb)^d conj(f(Tb))^e — do they CANCEL or ADD?
       If T were "generic" they'd be lower order; but T=mult-by-zeta is structured.

We compute, for each n and p:
  (i)   p*A_r(mu_n)             [LHS]
  (ii)  the binomial-expansion pieces, grouped, to find the recursion form.
  (iii) test the simplest candidate recursions:
        (C1) A_r(n) <= 2^? * A_r(n/2)  (pure L^infty-style -- expect FAIL by KB)
        (C2) A_r(n) <= sum_{j=0}^{2r} C(2r,j)^? * cross(j)  with cross expressed via A_*(n/2)
        (C3) the "Wick stability": does A_r(n)/Wick(n) <= A_r(n/2)/Wick(n/2)? (self-similar ratio)
"""
import cmath, math
from sympy import primitive_root
import numpy as np

def setup_zeta(n,p):
    for a in range(2,p):
        z=pow(a,(p-1)//n,p)
        if pow(z,n,p)==1 and pow(z,n//2,p)==p-1: break
    return z

def fvals(n_half, p):
    """f(b) = eta_b(mu_{n_half}) for all b in 0..p-1, as complex array (via FFT of indicator)."""
    # need a generator of mu_{n_half}
    for a in range(2,p):
        zz=pow(a,(p-1)//n_half,p)
        if pow(zz,n_half,p)==1 and (n_half==1 or pow(zz,n_half//2,p)==p-1): break
    mu=[pow(zz,j,p) for j in range(n_half)]
    ind=np.zeros(p)
    for x in mu: ind[x]=1.0
    # eta_b = sum_x e_p(b x) = conj-FFT? FFT[k]=sum_x ind[x] exp(-2pi i k x/p). We want +. use ifft*p or conj.
    F=np.fft.fft(ind)            # F[b]=sum_x ind[x] e^{-2pi i b x/p}
    return np.conj(F)            # eta_b = sum_x e^{+2pi i b x/p}

def doublefact(r):
    d=1.0
    for j in range(1,2*r,2): d*=j
    return d

def main():
    print("="*115)
    print("Test self-similar moment ratio:  is  A_r(n)/Wick(n)  <=  A_r(n/2)/Wick(n/2) ?")
    print("(If YES and decreasing, telescoping down to base mu_2/mu_4 closes the bound.)")
    print("="*115)
    for n,primes in [(16,[353,577,1153,4129]),(32,[1153,5857,32801]),(64,[2113,12289])]:
        print(f"\n##### n={n} vs n/2={n//2} #####")
        for p in primes:
            if (p-1)%n: continue
            # level n and n/2 moments via FFT
            fn   = fvals(n, p)      # eta_b(mu_n)
            fnh  = fvals(n//2, p)   # eta_b(mu_{n/2})
            magn  = np.abs(fn)**2
            magnh = np.abs(fnh)**2
            rmax=min(2*int(math.log2(n)), 10)
            print(f"  p={p} (beta={math.log(p)/math.log(n):.2f}):")
            print(f"     r |  A_r(n)/W(n) | A_r(n/2)/W(n/2) |  ratio[n]/[n/2] | (<=1 ?)")
            for r in range(1,rmax+1):
                Ar_n  = (magn[1:]**r).sum()/p
                Ar_nh = (magnh[1:]**r).sum()/p
                Wn  = doublefact(r)*n**r
                Wnh = doublefact(r)*(n//2)**r
                rn  = Ar_n/Wn
                rnh = Ar_nh/Wnh
                flag = "OK" if rn<=rnh+1e-9 else "VIOL"
                print(f"    {r:2d} |   {rn:8.4f}   |    {rnh:8.4f}     |    {rn/rnh:7.4f}     | {flag}")

if __name__=="__main__":
    main()
