import numpy as np
from sympy import primerange
import math
def doublefact(k):
    r=1.0
    for i in range(1,k+1): r*=(2*i-1)
    return r
def analyze(mu, beta_target):
    n=2**mu
    target=n**beta_target
    p=next(q for q in primerange(int(target), int(target*2)) if q%n==1)
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: break
    ind=np.zeros(p)
    for j in range(n): ind[pow(g,j,p)]=1.0
    eta=np.fft.fft(ind)
    mag2=np.abs(eta[1:])**2
    beta=math.log(p)/math.log(n)
    Mmax=math.sqrt(mag2.max())
    print(f"mu={mu} n={n} p={p} beta={beta:.2f}: mean|eta_b|^2={mag2.mean():.1f} (should=n={n}); M=max|eta|={Mmax:.1f}, M/sqrt(n log(p/n))={Mmax/math.sqrt(n*math.log(p/n)):.3f}", flush=True)
    print(f"     k | A_k/Wick (ratio) [A_k=(1/p)Sum|eta|^2k, Wick=(2k-1)!!n^k]")
    out="     "
    for k in range(1, min(mu+5, 13)):
        Ak=(mag2.astype(np.float64)**k).sum()/p
        wick=doublefact(k)*n**k
        out+=f"k{k}:{Ak/wick:.2f}  "
    print(out, flush=True)
for mu in [4,5,6]:
    analyze(mu,4); print()
