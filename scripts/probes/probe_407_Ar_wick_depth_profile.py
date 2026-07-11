import numpy as np
import sympy

# DECISIVE PROBE: is the DC-subtracted A_r = E_r - n^{2r}/q <= Wick=(2r-1)!!*n^r
# TRUE at the PRIZE DEPTH r ~ ln q, for n >= 64 (past the DC crossover that killed raw E_r)?
# The raw E_r <= Wick is FALSE for n>=64 (DC dominates). The claim is A_r (DC-removed) <= Wick.
# Test it EXACTLY via FFT of the mu_n indicator over Z/p.
#
# E_r = (1/q) sum_{all b} |eta_b|^{2r};  A_r = E_r - |G|^{2r}/q = (1/q) sum_{b!=0} |eta_b|^{2r}.
# Wick(r) = (2r-1)!! * n^r.

def dfac(m):
    # (2r-1)!! as float
    r = m
    prod = 1.0
    k = 2*r - 1
    while k >= 1:
        prod *= k
        k -= 2
    return prod

def prime_sub(n, beta):
    p = sympy.nextprime(int(n**beta))
    while (p-1) % n != 0:
        p = sympy.nextprime(p)
    return p

def period_sq(n, p):
    g = sympy.primitive_root(p); h = pow(g,(p-1)//n,p)
    G=set(); x=1
    for _ in range(n):
        G.add(x); x=(x*h)%p
    ind=np.zeros(p)
    for x in G: ind[x]=1.0
    mag=np.abs(np.fft.fft(ind))
    return mag**2   # |eta_b|^2, b=0..p-1

# keep p feasible for FFT (<~ 2e7). n=64 beta4 -> p~1.7e7 ok; n=128 beta3.4 ok; n=256 beta3.0 ok.
for (n, beta) in [(32, 4.5), (64, 4.0), (64, 3.7), (128, 3.4), (256, 3.0)]:
    p = prime_sub(n, beta)
    a = period_sq(n, p)         # |eta_b|^2
    q = float(p)
    lnq = np.log(q)
    rstar = int(round(lnq))
    print(f"n={n} beta={beta} p={p} q={q:.0f}  r*=round(ln q)={rstar}")
    nz = a[1:]                   # b != 0
    for r in sorted(set([2, 4, rstar//2 if rstar//2>=2 else 2, rstar, rstar+2])):
        if r < 1: continue
        # A_r = (1/q) sum_{b!=0} |eta_b|^{2r}; |eta_b|^2 already = a, so |eta_b|^{2r}=a^r
        Ar = (nz**r).sum() / q
        wick = dfac(r) * (n**r)
        ratio = Ar / wick
        flag = "OK A_r<=Wick" if ratio <= 1.0 else "*** A_r > Wick ***"
        print(f"    r={r}: A_r={Ar:.4e}  Wick={wick:.4e}  A_r/Wick={ratio:.4f}  {flag}")
