"""
P6-bessel-charp-transfer REFUTATION probe (#444).

POSITIVE ANGLE (proposed): the char-0 period CGF is (n/2)log I0(2t) (the Bessel/arcsine
baseline of INDEPENDENT angles). The prize would follow if the char-p deviation
    D(t) = log E_{b!=0}[exp(t*eta_b)] - (n/2) log I0(2t)
were <= 0 ("sub-baseline") for GENERIC prize primes, provable via subgroup equidistribution.
If true this gives M = max_b|eta_b| <= sqrt(2 n log m) (the SHARP, constant-sqrt2 floor).

THIS PROBE REFUTES THAT, two ways, over GENERIC (non-2-power, p != 2^k+1) primes,
proper mu_n = 2^mu subgroup, n | p-1, p PRIME, never n=p-1:

(1) D(t*) at the saddle t*=sqrt(2 log m / n) is > 0 for 5-7 of every 25 generic primes.
(2) D_opt = sup_t D(t) (the TRUE MGF gap, not a saddle artifact) is > 0 for 3-6 of every
    15 generic primes, with magnitude up to +1.47 -- i.e. the char-p MGF GENUINELY exceeds
    the char-0 Bessel baseline. The D_opt>0 primes are EXACTLY the ones with sharp-floor
    ratio R2 = M/sqrt(2 n log m) >= 1.0 (the genuine constant-sqrt2 violators).

CONCLUSION: D(t) <= 0 is FALSE for generic primes, so NO equidistribution result can
prove it. The proposed positive route is dead. The surviving (BGK-shape) bound is
M <= C sqrt(n log m) with C ~ 2 -- but even C=2 is exceeded at maximally-2-adic Fermat
primes (n=64, p=65537: R1 = M/sqrt(n log m) = 2.07). The floor is the BGK/Paley wall,
NOT a clean char-0 Bessel comparison.
"""
import numpy as np, math
from scipy.special import i0
from sympy import primitive_root
def isp(x):
    if x<2:return False
    if x%2==0:return x==2
    d=3
    while d*d<=x:
        if x%d==0:return False
        d+=2
    return True
def is_fermat_like(p):
    q=p-1; return (q & (q-1))==0   # p-1 a pure power of 2 == 2-power-structured field
def eta_arr(n,p):
    g=primitive_root(p); m=(p-1)//n; h=pow(g,(p-1)//n,p)
    mun=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64); w=2*math.pi/p
    reps=np.array([pow(g,j,p) for j in range(m)],dtype=np.int64)
    eta=np.empty(m)
    for i in range(0,m,8192):
        b=reps[i:i+8192][:,None]; eta[i:i+8192]=np.cos(w*((b*mun[None,:])%p)).sum(1)
    return m, eta
def lme(x): M=x.max(); return M+math.log(np.mean(np.exp(x-M)))

print("=== (1) D(t*) at saddle, generic primes: D>0 REFUTES sub-baseline ===")
for n in [16,32,64,128]:
    Ds=[]; t=((int(n**3.5))//n)*n+1; cnt=0
    while cnt<25:
        if t>n+1 and isp(t) and not is_fermat_like(t):
            m,eta=eta_arr(n,t); sad=math.sqrt(2*math.log(m)/n)
            Ds.append(lme(sad*eta)-(n/2)*math.log(i0(2*sad))); cnt+=1
        t+=n
    Ds=np.array(Ds)
    print(f"n={n:4d}: D(t*) in [{Ds.min():+.3f},{Ds.max():+.3f}] | #D>0: {int((Ds>1e-9).sum())}/25")

print("=== (2) sup_t D(t) (true MGF gap), generic primes: D_opt>0 = char-p EXCEEDS char-0 ===")
for n in [32,64,128]:
    res=[]; t=((int(n**3.0))//n)*n+1; cnt=0
    while cnt<15:
        if t>n+1 and isp(t) and not is_fermat_like(t):
            m,eta=eta_arr(n,t); Mx=eta.max(); sad=math.sqrt(2*math.log(m)/n)
            ts=np.linspace(0.05*sad,3*sad,60)
            Dopt=max(lme(tt*eta)-(n/2)*math.log(i0(2*tt)) for tt in ts)
            res.append((t,Dopt,Mx/math.sqrt(2*n*math.log(m)))); cnt+=1
        t+=n
    nab=sum(1 for _,d,_ in res if d>1e-6)
    print(f"n={n:4d}: #D_opt>0: {nab}/15, D_opt max {max(d for _,d,_ in res):+.3f}")
    for p,d,r in sorted(res,key=lambda x:-x[1])[:2]:
        print(f"        p={p}: D_opt={d:+.3f}  R2(sharp-floor ratio)={r:.3f}")

print("=== (3) C=2 NOT universal either: 2-power-structured Fermat F4 ===")
m,eta=eta_arr(64,65537); R1=eta.max()/math.sqrt(64*math.log(m))
print(f"n=64, p=65537=F4: R1 = M/sqrt(n log m) = {R1:.3f}  (> 2 => C=2 floor also violated at Fermat)")
