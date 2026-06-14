# Does A_r <= Wick=(2r-1)!!n^r persist up to r~log p? Extend in LOG space (avoid overflow).
import numpy as np
from sympy import primerange
import math
def analyze(mu, beta):
    n=2**mu; target=n**beta
    p=next(q for q in primerange(int(target), int(target*2)) if q%n==1)
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: break
    ind=np.zeros(p); 
    for j in range(n): ind[pow(g,j,p)]=1.0
    mag=np.abs(np.fft.fft(ind))[1:]   # |eta_b|, b!=0
    logmag=np.log(np.maximum(mag,1e-12))
    M=mag.max(); logp=math.log(p)
    ropt=int(round(logp/2))  # rough optimal r for moment
    print(f"mu={mu} n={n} p={p} beta={math.log(p)/math.log(n):.1f}: M={M:.1f}, M/sqrt(n log(p/n))={M/math.sqrt(n*math.log(p/n)):.3f}, ~r_opt={ropt}")
    print(f"   r | log(A_r/Wick) [<=0 means A_r<=Wick, moment route OK at this r] | (p*A_r)^(1/2r)/sqrt(n)")
    for r in [1,2,4,8,12,16,20,24,30,40]:
        # log A_r = log(1/p) + logsumexp(2r*logmag)
        logAr = -math.log(p) + (2*r*logmag).max() + math.log(np.exp(2*r*logmag - (2*r*logmag).max()).sum())
        logWick = math.log(math.factorial(2*r)) - r*math.log(2) - math.lgamma(r+1) + r*math.log(n)  # (2r-1)!!=(2r)!/(2^r r!)
        logWick = sum(math.log(2*i-1) for i in range(1,r+1)) + r*math.log(n)
        # M_bound = (p A_r)^{1/2r}
        Mbound = math.exp((math.log(p)+logAr)/(2*r))
        print(f"   {r:2d} | {(logAr-logWick):+7.2f}                                            | {Mbound/math.sqrt(n):.3f}")
for mu in [5,6]:
    analyze(mu,4); print()
