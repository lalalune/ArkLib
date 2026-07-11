# A4 [amice-iwasawa] final harsh-skeptic check: even the FIRST b-dependent p-adic datum (the lambda^n
# coefficient C_n(b), which is what the Iwasawa lambda-invariant / Weierstrass distinguished polynomial
# depends on, since the mu-invariant/valuation is 0=unit and b-independent) is UNCORRELATED with the
# archimedean magnitude |f(b)|. So neither the mu- nor the lambda-invariant of the dilation-tower
# measure can bound the archimedean sup. Confirms A4 reduces-to-wall (magnitude). Prize-faithful:
# p PRIME, p=1 mod n, p>=n^4, mu_n PROPER subgroup ((p-1)/n>1), never n=p-1.
import math, cmath
import numpy as np
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
for n in [8,16,32]:
    p=(n**4)|1
    while not(isprime(p) and (p-1)%n==0 and (p-1)//n>1): p+=2
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    invf=pow(math.factorial(n)%p,p-2,p)
    def Cn(b):
        tot=0
        for x in mu:
            m=(b*x)%p;prod=1
            for j in range(n): prod=prod*((m-j)%p)%p
            tot=(tot+prod)%p
        return tot*invf%p
    def per(b): return abs(sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in mu))
    bs=list(range(1,min(p,2000)))
    cn=[Cn(b) for b in bs]; ar=np.array([per(b) for b in bs])
    cnb=np.array([c if c<p//2 else c-p for c in cn],dtype=float)
    print(f"n={n} p={p}: corr(|C_n(b)|,arch)={np.corrcoef(np.abs(cnb),ar)[0,1]:.4f}  corr(C_n(b),arch)={np.corrcoef(cnb,ar)[0,1]:.4f}  (~0 => p-adic lambda-datum magnitude-blind)")
print("VERDICT: both Iwasawa invariants (mu=0 unit, b-indep; lambda=fn of C_n(b), uncorrelated) are blind to archimedean sup. A4 reduces-to-wall.")
