import math
# Angle A (moment problem), done directly: how many LOW moments must be fixed before the partial cosh-sum
# captures the bulk of Sigma cosh(eta_b y*)?  cosh has all-positive terms, so the truncation
#   T_R = Sum_{r<=R} (q A_r) y*^{2r}/(2r)!   is a LOWER bound on the true Sigma_{b!=0} cosh(eta_b y*) = q*Phi_nz.
# The saddle sits at r* = n y*^2/2 = ln q. If T_R reaches the bulk only for R ~ r* ~ ln q, the LOW moments do
# NOT determine the sum => deep moments load-bearing => angle A reduces to the wall.
# We compute, at the prize regime, the fraction of the full sum captured by depth R, vs R/r*.
def isprime(z):
    if z<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if z%q==0:return z==q
    d=z-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,z)
        if x in(1,z-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%z
            if x==z-1:ok=True;break
        if not ok:return False
    return True
def prroot(p):
    f=[];m=p-1;dd=2
    while dd*dd<=m:
        if m%dd==0:
            f.append(dd)
            while m%dd==0:m//=dd
        dd+=1
    if m>1:f.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//x,p)!=1 for x in f):return g
def real_periods(n,p,g):
    zeta=pow(g,(p-1)//n,p); D=[pow(zeta,i,p) for i in range(n)]
    m=(p-1)//n; tp=2*math.pi/p; out=[]; gj=1
    for j in range(m):
        re=sum(math.cos(((gj*x)%p)*tp) for x in D); out.append(re); gj=(gj*g)%p
    return out,m
print("Angle A moment problem: fraction of Sigma cosh captured by depth R, vs R/r* (r*=ln q = saddle depth).")
print("If bulk needs R ~ r* (not R=O(1)), LOW moments don't determine the sum => reduces to wall.")
for mu in [4,5,6]:
    n=2**mu; lo=n**4; p=lo|1
    while not((p-1)%n==0 and isprime(p)): p+=2
    g=prroot(p); reals,m=real_periods(n,p,g); q=p; lnq=math.log(q)
    ystar=math.sqrt(2*lnq/n); rstar=lnq
    # full sum over b!=0 = n * sum_j cosh(reals[j] ystar)
    full=n*sum(math.cosh(v*ystar) for v in reals)
    # partial by depth R: T_R = n * sum_j sum_{r<=R} (reals[j] ystar)^{2r}/(2r)!
    print(f"  n={n} p={p} r*=ln q={rstar:.1f}  full Sigma cosh / q^2 = {full/q**2:.4f}")
    cum=[0.0]*(int(2*rstar)+5)
    for v in reals:
        z=v*ystar; term=1.0  # r=0 term =1
        for r in range(1,len(cum)):
            term*= (z*z)/((2*r)*(2*r-1))   # ratio (z^2)/((2r)(2r-1)) builds z^{2r}/(2r)!
            cum[r]+=term
    # cumulative fraction
    base=n*len(reals)  # r=0 contributes 1 each
    running=base
    for R in [1,2,3,5,int(rstar*0.5),int(rstar),int(rstar*1.5),int(2*rstar)]:
        s=base+sum(n*cum[r] for r in range(1,min(R+1,len(cum))))
        print(f"     R={R:>3} (R/r*={R/rstar:4.2f}):  captured fraction = {s/full:7.4f}")
print("DONE")
