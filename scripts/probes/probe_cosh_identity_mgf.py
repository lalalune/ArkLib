import numpy as np, math, cmath
# TEST the exact cancellation identities the user's idea leads to:
# (1) sqrt(p) cancels: eta_b = (sqrt(p)/m) * sum_j chibar^j(b)*u_j, u_j = tau(chi^j)/sqrt(p) UNIT.
#     => M = sqrt(n/m)*R, R = max_b |sum_j chibar^j(b) u_j| = resonance of m unit Gauss-phases.
# (2) cosh generating-function identity (char-0): sum_{b in F_p} cosh(|eta_b|*y) = p * I0(2y)^{n/2}.
#     This eliminates the MAX (turns sup-norm into an MGF) and shows char-0 sub-Gaussianity transparently.
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
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)):return g
def i0(z):  # modified Bessel I0
    # series sum (z/2)^{2k}/(k!)^2
    s=0.0;t=1.0;k=0
    while t>1e-18*max(s,1) or k<5:
        s+=t;k+=1;t=(z/2)**(2*k)/(math.factorial(k)**2)
        if k>400:break
    return s
for p,n in [(4129,8),(12289,8),(40961,8),(786433,16)]:
    if (p-1)%n: continue
    g=proot(p)
    mu=[pow(pow(g,(p-1)//n,p),i,p) for i in range(n)]
    # all eta_b for b in F_p
    absb=np.empty(p)
    for b in range(p):
        s=sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in mu)
        absb[b]=abs(s)
    # identity (2): sum_b cosh(|eta_b|*y) vs p*I0(2y)^{n/2}, several y
    print(f"p={p} n={n} m={(p-1)//n}: cosh-identity  sum_b cosh(|eta|y) vs p*I0(2y)^(n/2)",flush=True)
    for y in [0.2,0.5,1.0]:
        lhs=np.cosh(absb*y).sum()
        rhs=p*i0(2*y)**(n/2)
        print(f"    y={y}: LHS={lhs:.4f}  RHS={rhs:.4f}  ratio={lhs/rhs:.6f}",flush=True)
    # the sup-norm bound from the identity: M*y <= arccosh(sum_{b!=0} cosh) ; optimize over y
    M=absb[1:].max() if p>1 else 0  # max over b!=0
    best=1e9
    for y in np.linspace(0.01,3,300):
        rhs=p*i0(2*y)**(n/2)-math.cosh(n*y)
        if rhs>1: best=min(best,math.acosh(rhs)/y)
    print(f"    true M(max b!=0)={M:.4f}  | cosh-identity UPPER bound min_y arccosh(.)/y = {best:.4f}  | floor sqrt(2n log m)={math.sqrt(2*n*math.log((p-1)//n)):.4f}",flush=True)
print("DONE")
