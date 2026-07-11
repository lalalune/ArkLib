#!/usr/bin/env python3
# Does the K_eff plateau translate to the BGK constant, and how tightly? (unify the two forms)
# Moment method: M^{2r} <= sum_{b!=0} eta_b^{2r} = n * sum_T eta_t^{2r} = n*p*E_r'  (E_r'=(1/p)sum_T eta^{2r})
#   => M <= (n p E_r')^{1/2r}; with E_r'~K^r (2r-1)!! n^r and optimal r~ln q  =>  M <~ sqrt(2K) sqrt(n ln q).
# Define  C_direct = M / sqrt(n * ln(q/n))   (the BGK constant the swarm measures)
#         C_moment = min_r (n p E_r')^{1/2r} / sqrt(n ln(q/n))   (the energy/moment-method bound on C)
# Compare: if C_moment ~ C_direct, the energy route is tight (bounded-K => bounded-C => prize);
#          if C_moment >> C_direct, the moment method is lossy.
import math, numpy as np
def isp(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True
def proot(p):
    m=p-1; fs=[]; d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.append(m)
    g=2
    while not all(pow(g,(p-1)//f,p)!=1 for f in fs): g+=1
    return g
def v2(x):
    v=0
    while x%2==0: x//=2; v+=1
    return v
def good_prime(n,lo):
    mu2=int(round(math.log2(n))); p=lo+((1+n-lo%n)%n)
    while not (p%n==1 and isp(p) and v2(p-1)==mu2): p+=n
    return p
def dfact(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v
def analyze(n):
    p=good_prime(n,n**4); g=proot(p); h=pow(g,(p-1)//n,p); m=(p-1)//n; gn=pow(g,n,p)
    mu=[pow(h,j,p) for j in range(n)]
    b=1; bl=[0]*m
    for k in range(m): bl[k]=b; b=b*gn%p
    barr=np.array(bl,dtype=np.int64); acc=np.zeros(m,dtype=np.float64); c=2*np.pi/p
    for x in mu: acc+=np.cos(c*((barr*int(x))%p))
    M=np.abs(acc).max()
    e2=acc*acc
    lnq=math.log(p); lnqn=math.log(p/n); rmax=int(1.6*lnq)
    # moment-method bound on M: min_r (n*p*E_r')^{1/2r}, E_r'=(1/p) sum_T eta^{2r}
    Mbound=float('inf'); Kpk=0.0
    for r in range(1,rmax+1):
        Er=np.sum(e2**r)/p
        mb=(n*p*Er)**(1.0/(2*r))
        if mb<Mbound: Mbound=mb
        k=(Er/(dfact(r)*(n**r)))**(1.0/r)
        if k>Kpk: Kpk=k
    Cd=M/math.sqrt(n*lnqn); Cm=Mbound/math.sqrt(n*lnqn)
    Cpred=math.sqrt(2*Kpk*lnq/lnqn)   # sqrt(2K * beta/(beta-1))
    return p,m,M,Kpk,Cd,Cm,Cpred,lnq/math.log(n)
def main():
    print("# unify K_eff plateau <-> BGK constant. C_direct=M/sqrt(n ln(q/n)); C_moment=moment bound; C_pred=sqrt(2K b/(b-1))")
    print(f"# {'n':>4} {'beta':>5} {'M':>8} {'Kpeak':>6} {'C_direct':>8} {'C_moment':>8} {'C_pred':>7} {'mom/dir':>7}")
    for n in (32,64,128):
        p,m,M,Kpk,Cd,Cm,Cpred,beta=analyze(n)
        print(f"  {n:>4} {beta:>5.2f} {M:>8.3f} {Kpk:>6.3f} {Cd:>8.3f} {Cm:>8.3f} {Cpred:>7.3f} {Cm/Cd:>7.3f}")
    print()
    print("READ: C_direct is the BGK constant (swarm measures ~1.31-1.45).")
    print("      C_moment ~ C_direct => energy/moment route is TIGHT (bounded-K plateau => bounded BGK C => prize).")
    print("      C_moment >> C_direct => moment method loses a factor (K-plateau does NOT directly give the sup).")
if __name__=='__main__':
    main()
