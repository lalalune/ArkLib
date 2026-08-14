"""
Tool 5 depth-sparsity core utilities.
mu_n = group of n-th roots of unity in F_p (n=2^mu, p prime, n | p-1).
E_r = (1/q) sum_b |eta_b|^{2r} = #{(x_1..x_r,y_1..y_r) in mu_n^{2r}: sum x = sum y}.
Since -1 in mu_n, equivalently #{2r-tuples from mu_n summing to 0}.
Wick (char-0 pairing) term = (2r-1)!! n^r.
Cumulant excess = sum_{b!=0}|eta_b|^{2r} - char0_excess... we grade E_r itself by collision depth.
"""
import sympy, numpy as np
from math import comb

def dfac(r):
    # (2r-1)!!
    prod=1
    k=2*r-1
    while k>=1:
        prod*=k; k-=2
    return prod

def prime_sub(n, beta, avoid_high_v2=False):
    """Prime p ~ n^beta with n | p-1. If avoid_high_v2 False, just take next."""
    p = sympy.nextprime(int(n**beta))
    while (p-1)%n != 0:
        p = sympy.nextprime(p)
    return p

def fermat_like_prime(n, target_beta):
    """Find a prime with HIGH 2-adic valuation of p-1 (structured) near n^beta."""
    best=None
    lo=int(n**target_beta)
    p=sympy.nextprime(lo)
    cands=[]
    while p < lo*4:
        if (p-1)%n==0:
            t=p-1; v2=0
            while t%2==0: t//=2; v2+=1
            cands.append((v2,p))
        p=sympy.nextprime(p)
        if len(cands)>4000: break
    cands.sort(reverse=True)  # highest v2 first
    return cands[0][1] if cands else prime_sub(n,target_beta)

def mu_group(n, p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    G=[]; x=1
    for _ in range(n):
        G.append(x); x=(x*h)%p
    return G

def period_sq(n,p):
    """|eta_b|^2 for all b via FFT."""
    G=mu_group(n,p)
    ind=np.zeros(p)
    for x in G: ind[x]=1.0
    mag=np.abs(np.fft.fft(ind))
    return mag**2

def E_r_fft(n,p,r):
    """Exact E_r = (1/q) sum_b |eta_b|^{2r}."""
    a=period_sq(n,p)
    q=float(p)
    # round to nearest int (FFT) — for verification use integer counts where feasible
    val = (a**r).sum()/q
    return val
