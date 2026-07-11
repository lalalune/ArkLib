import numpy as np
from sympy import isprime, factorint

# Robustness: confirm DC A_r thinness-essentiality at n=16 (not just n=32). FFT period spectrum.
# n=16: thick window ~ beta 2.3-3.2, thin >= 4. Test structured (high v2) primes in BOTH windows.
def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def primroot(p):
    from sympy import primitive_root
    return primitive_root(p)

def Ar_profile(n,p,rmax):
    g=primroot(p); gen=pow(g,(p-1)//n,p)
    mu=[pow(gen,j,p) for j in range(n)]
    ind=np.zeros(p)
    for x in mu: ind[x]=1.0
    spec=np.fft.fft(ind); a2=spec.real**2+spec.imag**2
    q=p; out=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q; Ar=Er-(n**(2*r))/q
        out.append((r, Ar/(dfact(2*r-1)*n**r)))
    return out

n=16
# pick structured (high v2) primes across beta windows
buckets={'thick(2.3-3.2)':[], 'thin(>=4)':[]}
for p in range(n+1, 200000):
    if p%n==1 and isprime(p):
        beta=np.log(p)/np.log(n); v2=factorint(p-1).get(2,0)
        if 2.3<=beta<=3.2 and v2>=8 and len(buckets['thick(2.3-3.2)'])<3:
            buckets['thick(2.3-3.2)'].append((p,v2,beta))
        if beta>=3.95 and v2>=8 and len(buckets['thin(>=4)'])<3:
            buckets['thin(>=4)'].append((p,v2,beta))
print(f"n={n} DC A_r/Wick at structured primes (high 2-adic), by window:")
for win,lst in buckets.items():
    for p,v2,beta in lst:
        rmax=min(int(2*np.log((p-1)//n))+1,13)
        prof=Ar_profile(n,p,rmax); mx=max(prof,key=lambda t:t[1])
        cross=[r for r,rat in prof if rat>1.0001]
        print(f"  [{win}] p={p} beta={beta:.2f} v2={v2}: max A_r/Wick={mx[1]:.3f}@r={mx[0]} cross={cross if cross else 'NONE'}")
