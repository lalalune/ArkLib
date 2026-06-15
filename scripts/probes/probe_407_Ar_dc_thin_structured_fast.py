import numpy as np
from sympy import isprime, primitive_root, factorint

# FAST: |eta_b|^2 for all b = |FFT of indicator(mu_n)|^2 (the period spectrum), O(p log p).
# eta_b = sum_{x in mu} e_p(b x) = DFT of 1_{mu_n} at frequency b. So a2 = |np.fft.fft(ind)|^2.
def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def Ar_profile(n,p,rmax):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=[pow(gen,j,p) for j in range(n)]
    ind=np.zeros(p)
    for x in mu: ind[x]=1.0
    spec=np.fft.fft(ind)
    a2=(spec.real**2+spec.imag**2)  # |eta_b|^2 for b=0..p-1
    q=p; out=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q; Ar=Er-(n**(2*r))/q
        out.append((r, Ar/(dfact(2*r-1)*n**r)))
    return out

n=32
target=n**4
cands=[]
for p in range(target, target+600000):
    if p%n==1 and isprime(p):
        v2=factorint(p-1).get(2,0); beta=np.log(p)/np.log(n)
        if beta>=3.95: cands.append((p,v2,beta))
cands.sort(key=lambda t:-t[1])
print(f"n={n} THIN (beta>=3.95) structured primes by 2-adic part — does DC A_r cross Wick at deep r?")
for p,v2,beta in cands[:5]:
    rmax=min(int(2*np.log((p-1)//n))+1, 14)
    prof=Ar_profile(n,p,rmax)
    mx=max(prof,key=lambda t:t[1]); cross=[r for r,rat in prof if rat>1.0001]
    logm=np.log((p-1)//n)
    print(f"  p={p} beta={beta:.3f} v2={v2} logm={logm:.1f}: max A_r/Wick={mx[1]:.3f}@r={mx[0]}  cross={cross if cross else 'NONE'}")

# control: the thick Fermat n=32 p=65537 should cross (sanity)
print("control thick Fermat n=32 p=65537 (beta=3.20):")
prof=Ar_profile(32,65537,14); mx=max(prof,key=lambda t:t[1])
print(f"  max A_r/Wick={mx[1]:.3f}@r={mx[0]} cross={[r for r,rat in prof if rat>1.0001]}")
