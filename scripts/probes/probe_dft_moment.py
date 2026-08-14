import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ntlib_pg import isprime, primitive_root
import numpy as np, math, itertools
def gauss_sums(p,n):
    g=primitive_root(p); m=(p-1)//n
    dlog=np.empty(p,dtype=np.int64); x=1
    for k in range(p-1): dlog[x]=k; x=x*g%p
    w=np.exp(2j*np.pi/p); xs=np.arange(1,p); a=dlog[xs].astype(np.float64); ex=w**xs
    E=np.empty(p-1,dtype=complex); E[a.astype(int)]=ex; avec=np.arange(p-1)
    G=np.empty(m,dtype=complex)
    for t in range(m): G[t]=(np.exp(2j*np.pi*((n*t)%(p-1))*avec/(p-1))*E).sum()
    return G,m
# pick n=4, small prime so m tiny
for n in [4]:
    # primes p ≡ 1 mod 4, small
    for p in [13,17,29,37]:
        if (p-1)%n: continue
        G,m=gauss_sums(p,n)
        eta=np.fft.fft(G)/m
        for r in [2,3]:
            lhs=(np.abs(eta)**(2*r)).sum()
            rhs=0j
            for t in itertools.product(range(m),repeat=r):
                st=sum(t)
                for tp in itertools.product(range(m),repeat=r):
                    if (st-sum(tp))%m==0:
                        rhs+= np.prod([G[i] for i in t])*np.conj(np.prod([G[j] for j in tp]))
            rhs/=m**(2*r-1)
            print(f"n={n} p={p} m={m} r={r}: LHS={lhs:.5f} RHS={rhs.real:.5f} match={abs(lhs-rhs.real)<1e-5}")
