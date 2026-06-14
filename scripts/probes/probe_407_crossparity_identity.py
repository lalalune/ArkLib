#!/usr/bin/env python3
import cmath, math
def isprime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prim_root_order(n, p):
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: return g
    raise RuntimeError
def periods(H,p):
    w=2j*math.pi/p
    return [sum(cmath.exp(w*((b*x)%p)) for x in H) for b in range(p)]
def check(n,p):
    g=prim_root_order(n,p)      # order n; g^{n/2} = -1
    zeta=g                       # zeta^{n/2} = -1, so zeta*mu_{n/2} = negative-half
    Hk1=[pow(g,2*j,p) for j in range(n//2)]  # mu_{n/2} = squares = <g^2>
    P1=periods(Hk1,p)
    sum_cross=sum(2.0*(P1[b]*P1[(b*zeta)%p].conjugate()).real for b in range(1,p))
    pred=-(n*n)//2
    ok=abs(sum_cross-pred)<1e-5
    print(f"  n={n:3d} p={p:5d}: sum_b!=0 X = {sum_cross:+11.4f}  pred -n^2/2={pred:6d}  {'OK' if ok else '**FAIL**'}")
    return ok
allok=True
for n in [8,16,32,64]:
    cnt=0
    for p in range(n+1,6000):
        if (p-1)%n==0 and isprime(p):
            allok &= check(n,p); cnt+=1
            if cnt>=5: break
print("ALL OK" if allok else "SOME FAILED")
