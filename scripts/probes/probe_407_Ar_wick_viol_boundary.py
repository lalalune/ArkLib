import numpy as np
from sympy import isprime, primitive_root, factorint
# Locate the A_r>Wick violation boundary in beta. Is it confined to THICK (beta<~3.2), or does
# it reach the PRIZE band (beta 4-5)? Test n=32 across many primes, full beta sweep, report
# max_r A_r/Wick and the beta at which violations vanish.

def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def Ar_ratios(n,p,rmax):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=np.array([pow(gen,j,p) for j in range(n)])
    a2=np.empty(p)
    for b in range(p):
        a2[b]=abs(np.exp(2j*np.pi*(b*mu % p)/p).sum())**2
    q=p; out=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q
        Ar=Er-(n**(2*r))/q
        out.append(Ar/(dfact(2*r-1)*(n**r)))
    return out

n=32
print(f"n={n}: max_r A_r/Wick across beta. p=1217 (beta~2.05) violated. Where does it stop?")
# collect primes across beta bins
import collections
bins=collections.defaultdict(list)
for p in range(n+1, 200000):
    if p%n==1 and isprime(p):
        beta=np.log(p)/np.log(n)
        b=round(beta*2)/2  # 0.5 bins
        if len(bins[b])<4 and 2.0<=beta<=5.2:
            bins[b].append(p)
for b in sorted(bins):
    for p in bins[b]:
        if p>150000: continue
        rmax=min(int(2*np.log((p-1)//n))+1, 12)
        rats=Ar_ratios(n,p,rmax)
        mx=max(rats); mxr=int(np.argmax(rats))+1
        beta=np.log(p)/np.log(n)
        viol = "  *** A_r>Wick ***" if mx>1.0001 else ""
        print(f"  beta={beta:.2f} p={p}: max A_r/Wick={mx:.4f} (r={mxr}){viol}")
