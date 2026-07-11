import numpy as np
from math import log, sqrt
def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x==1 or x==n-1:continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True
def subgroup_gen(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if h==1 or pow(h,n//2,p)==1:continue
        S=[];x=1
        for _ in range(n):x=(x*h)%p;S.append(x)
        if len(set(S))==n:return sorted(set(S)),h
    return None,None
def periods(p,S):
    b=np.arange(p);eta=np.zeros(p,dtype=complex);ang=2j*np.pi/p
    for x in S:eta+=np.exp(ang*((b*x)%p))
    return eta
print("=== RUDIN-SHAPIRO FLATNESS TEST for the 2-power Gauss-period tower ===")
print("Parallelogram: ||eta_b(mu_n)||^2 + ||eta^chi_b(mu_n)||^2 = 2(||A||^2+||B||^2),")
print("A=eta_b(mu_{n/2}), B=eta_{b*zeta}(mu_{n/2}). RS-FLAT <=> ||A||^2+||B||^2 = const(=2n).")
print("Measure CV = std/mean of g(b):=||eta_b(mu_{n/2})||^2 + ||eta_{b*zeta}(mu_{n/2})||^2 over b!=0.\n")
for n in [16,32,64,128,256]:
    # need mu_n and mu_{n/2}; zeta generates mu_n (order n)
    for tgt in [40,200,1000]:
        p=None
        for m in range(tgt,tgt*5):
            cand=n*m+1
            if isprime(cand):
                op=cand-1
                while op%2==0:op//=2
                p=cand;break
        if p is None or p>600000:continue
        Sn,zeta=subgroup_gen(p,n)
        if Sn is None:continue
        # mu_{n/2} = <zeta^2>
        h2=zeta
        Sh=[];x=1
        for _ in range(n//2):x=(x*pow(h2,2,p))%p;Sh.append(x)
        Sh=sorted(set(Sh))
        if len(Sh)!=n//2:continue
        etah=periods(p,Sh)   # periods of mu_{n/2}
        mag2=np.abs(etah)**2
        b=np.arange(p)
        bz=(b*zeta)%p
        g=mag2 + mag2[bz]    # ||eta_b(mu_{n/2})||^2 + ||eta_{b zeta}(mu_{n/2})||^2
        gnz=g[1:]            # b!=0
        cv=gnz.std()/gnz.mean()
        # also: M(mu_n)/sqrt(n) for reference
        etan=periods(p,Sn);Mn=sqrt((np.abs(etan[1:])**2).max())
        print(f"n={n:4d} p={p:7d} idx={(p-1)//n:5d} | mean(g)={gnz.mean():.1f} (2n={2*n}) CV(g)={cv:.3f} | M(mu_n)/sqrt(n)={Mn/sqrt(n):.2f}")
    print()
print("RS-FLAT would need CV(g)->0 (g approx constant 2n). Large/growing CV => NOT flat => drift open.")
