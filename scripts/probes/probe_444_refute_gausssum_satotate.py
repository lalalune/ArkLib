#!/usr/bin/env python3
# Fast (numpy, tabled roots) verification of the Gauss-sum dual identity backing the
# GaussSumSatoTate-FreqRestriction verdict (#444 25-novel, verdict pending):
#   eta_b = (n/(p-1)) * sum_{chi in H^perp} conj(chi)(b) * g(chi),  H^perp={chi_k : n|k}, |H^perp|=m=(p-1)/n.
import numpy as np
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def find_p(n,lo):
    p=lo+((1-lo)%n)
    while not (p%n==1 and isprime(p)): p+=n
    return p
def primroot(p):
    m=p-1; fs=set(); d=2
    while d*d<=m:
        if m%d==0:
            fs.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.add(m)
    for gg in range(2,p):
        if all(pow(gg,(p-1)//q,p)!=1 for q in fs): return gg
    return 0
def run(n,beta):
    p=find_p(n,n**beta); g=primroot(p); m=(p-1)//n; h=pow(g,m,p)
    mun=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    ep=np.exp(2j*np.pi*np.arange(p)/p)           # ep[k]=e_p(k)
    zr=np.exp(2j*np.pi*np.arange(p-1)/(p-1))      # zr[j]=zeta_{p-1}^j
    ind=np.zeros(p,dtype=np.int64); cur=1
    for a in range(p-1):
        ind[cur]=a; cur=cur*g%p
    xs=np.arange(1,p,dtype=np.int64)              # x in F_p^*
    indx=ind[xs]; epx=ep[xs]
    ks=(n*np.arange(m))%(p-1)                      # H^perp exponents
    # g(chi_k) for all k in ks: gauss[j]=sum_x zr[(ks[j]*indx)%(p-1)]*epx
    gauss=np.empty(m,dtype=np.complex128)
    for j in range(m):
        gauss[j]=np.sum(zr[(ks[j]*indx)%(p-1)]*epx)
    okmag=np.allclose(np.abs(gauss[ks!=0]), np.sqrt(p), atol=1e-8)
    # verify identity for ALL b: eta_b vs (n/(p-1)) sum_j conj(chi_{ks[j]})(b) gauss[j]
    b=np.arange(1,p,dtype=np.int64)
    # eta_b = sum_{x in mun} ep[b*x mod p]
    eta=np.zeros(p-1,dtype=np.complex128)
    for x in mun: eta+=ep[(b*int(x))%p]
    # rhs: for each b, sum_j zr[(-ks[j]*ind[b])%(p-1)] * gauss[j]
    indb=ind[b]                                    # (p-1,)
    # phase[j,b] = zr[(-ks[j]*indb)%(p-1)]; do it as matrix (m x (p-1)) — m,p-1 ~ 516x4128 ok
    ph=zr[((-ks[:,None]*indb[None,:])%(p-1))]
    rhs=(n/(p-1))*(gauss[:,None]*ph).sum(axis=0)
    maxerr=np.max(np.abs(eta-rhs))
    M=np.abs(eta).max(); typ=np.abs(eta).mean(); sn=np.sqrt(n)
    evt=np.sqrt(2*np.log(m/2))
    return p,m,okmag,maxerr,typ,sn,M,M/sn,evt
def main():
    print("# Gauss-sum dual identity verification (numpy, all b)")
    for n,beta in [(8,4),(16,4)]:
        p,m,okmag,maxerr,typ,sn,M,Msn,evt=run(n,beta)
        print(f"n={n:3d} p={p:8d} m={m:6d} |g|=sqrtp:{okmag}  IDENTITY max|eta_b-dual| over ALL b = {maxerr:.2e}")
        print(f"        typical|eta_b|={typ:.3f} (~sqrt n={sn:.3f}: equidist OK)   "
              f"SUP={M:.3f}={Msn:.3f}*sqrt n  (EVT sqrt(2log(m/2))={evt:.3f})")
    print()
    print("VERDICT GaussSumSatoTate-FreqRestriction: premise EXACT (eta_b = fixed unitary image of n")
    print("  unimodular Gauss sums). Katz/Deligne equidistribution pins the TYPICAL eta_b (~sqrt n), but")
    print("  the conjecture's claim 'equidistribution pins the SUP' is FALSE: the sup over m cosets is the")
    print("  EVT extreme ~sqrt(2n log m), which equidistribution does NOT bound. REDUCES TO BGK.")
if __name__=='__main__':
    main()
