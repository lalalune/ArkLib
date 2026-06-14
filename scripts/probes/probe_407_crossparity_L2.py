#!/usr/bin/env python3
"""
Two more candidate CLEAN identities for the cross term X(b)=2Re(P1(b) conj P1(bz)):
 (I2) sum_{b} X(b)^2  (L^2 of the cross term) -- is it clean / p-indep?
 (I3) sum_{b!=0} |P_k(b)|^2 = sum_{b!=0}(|P1(b)|^2+|P1(bz)|^2) + sum_{b!=0}X(b)
      = (p*n/2 - (n/2)^2)*2 + (-n^2/2) = p*n - n^2  [matches Parseval for mu_n]  -> consistency
 (I4) the FOURTH-moment / energy bridge: does sum_b X(b)^2 relate to additive energy E_2(mu_{n/2})?
"""
import cmath, math
def isprime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prim_root_order(n,p):
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: return g
    raise RuntimeError
def periods(H,p):
    w=2j*math.pi/p
    return [sum(cmath.exp(w*((b*x)%p)) for x in H) for b in range(p)]
def analyze(n,p):
    g=prim_root_order(n,p); zeta=g
    Hk1=[pow(g,2*j,p) for j in range(n//2)]
    P1=periods(Hk1,p)
    X=[2.0*(P1[b]*P1[(b*zeta)%p].conjugate()).real for b in range(p)]
    # I2 sum_b X^2 (all b incl 0)
    L2_all=sum(X[b]**2 for b in range(p))
    L2_nz =sum(X[b]**2 for b in range(1,p))
    X0=X[0]  # = n^2/2
    # candidate closed forms involving p, n
    print(f"n={n:3d} p={p:5d}: X(0)={X0:.1f}(n^2/2={n*n/2}) | sum_b X^2(all)={L2_all:.1f} | "
          f"sum_b!=0 X^2={L2_nz:.1f} | /p={L2_nz/p:.3f} | -X0^2+L2_all={L2_all-X0**2:.1f}")
for n in [8,16,32]:
    cnt=0
    for p in range(n+1,5000):
        if (p-1)%n==0 and isprime(p):
            analyze(n,p); cnt+=1
            if cnt>=5: break
    print()
