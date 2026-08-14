import numpy as np, sys
from sympy import isprime, primitive_root

def maxeta(p, n):
    g = primitive_root(p)
    m = (p-1)//n
    cur = pow(g, m, p)
    a = np.zeros(p)
    x = 1
    for j in range(n):
        a[x] = 1.0
        x = (x*cur) % p
    F = np.fft.fft(a); F[0]=0
    return float(np.max(np.abs(F)))

def v2(x):
    c=0
    while x%2==0: x//=2; c+=1
    return c

# n-scaling of worst-over-K minimal-2adic (m odd) primes. K fixed, p capped small for speed.
K=25; PCAP=1_500_000
print("=== n-scaling: worst-over-K=25 minimal-2adic(m ODD) primes, p<1.5M ===", flush=True)
for mu in range(3,13):
    n=2**mu
    Cs=[]
    m=3
    while len(Cs)<K and m<300000:
        if m%2==1:
            p=m*n+1
            if p>PCAP: break
            if isprime(p):
                M=maxeta(p,n); fl=np.sqrt(2*n*np.log(p/n))
                Cs.append(M/fl)
        m+=1
    if len(Cs)<5:
        print(f"n=2^{mu}: only {len(Cs)} primes <PCAP, skip", flush=True); continue
    Cs=np.array(Cs)
    print(f"n=2^{mu:2d}={n:6d} K={len(Cs):2d} median={np.median(Cs):.3f} worst={Cs.max():.3f} "
          f"#>1={int((Cs>1).sum())} #>1.2={int((Cs>1.2).sum())}", flush=True)
