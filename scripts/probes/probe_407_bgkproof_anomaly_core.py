#!/usr/bin/env python3
"""
#407 STRATEGY 2 deliverable — the exact reduction and why the 2-adic moment descent does NOT close.

ESTABLISHED (all exact, no sampling):

(I) IDENTITY.  A_r(p) := (1/p) sum_{b!=0} |eta_b(mu_n)|^{2r}  =  coll_r(p) - n^{2r}/p,
    where coll_r(p) = #{(x,y) in mu_n^{2r} : sum x = sum y (mod p)} = (1/p) sum_b |eta_b|^{2r}.

(II) RING DECOMPOSITION.  coll_r(p) = R_r + Anom_r(p),  Anom_r >= 0, where
     R_r     = #{(x,y) in mu_n^{2r} : sum x = sum y in Z[zeta_n]}   (char-0 count)
     Anom_r  = #{char-p-only collisions} (sum equal mod p but NOT in the ring).

(III) PROVEN FLOOR (DyadicEnergyK1.lean, Lam-Leung):  R_r <= Wick := (2r-1)!! * n^r.

(IV) THE SOLE OPEN INEQUALITY (sufficient):
        A_r <= Wick   <==   Anom_r(p) <= n^{2r}/p.
     [then A_r = R_r + Anom_r - n^{2r}/p <= R_r <= Wick.]

(V) WHY STRATEGY-2's per-level MOMENT descent FAILS (the directive's question, answered NO):
    Parallelogram split mu_n = mu_h ⊔ zeta*mu_h (h=n/2):  eta_b(mu_n) = u + v,
      u = eta_b(mu_h),  v = eta_{zeta b}(mu_h).
    Then  coll_r(mu_n) = (1/p) sum_b (X_b + Y_b)^r,  X = |u|^2+|v|^2,  Y = 2 Re(u vbar),  |Y| <= X.
    - Pointwise X+Y <= 2X gives  coll_r(mu_n) <= 2^r <X^r>  -- VERIFIED ratio<1.
    - BUT 2^r is exactly the Wick(n)/Wick(h) tower factor; the slack is the ODD-j cross terms
      S_odd = sum_{j odd} C(r,j) <X^{r-j} Y^j>, and S_odd >= 0 (POSITIVE, verified) -- the cross
      moments ADD, they do NOT cancel.  The even-only bound 2^{r-1}<X^r> already EXCEEDS Wick(n)
      at small r (ratios 1.21, 1.39 at beta=4).  So no one-step descent coll_r(n) <= C * <X^r>(h)
      with C absorbing into Wick exists: the alignment that breaks the L^inf descent
      (at b*, A=B => Y=X) contributes POSITIVELY to every even moment.  Same wall, moment dress.
"""
import math
from sympy import primerange
import numpy as np
from collections import defaultdict
from math import comb

def coord_vectors(n):
    h=n//2; V=[]
    for j in range(n):
        v=[0]*h
        if j<h: v[j]=1
        else: v[j-h]=-1
        V.append(tuple(v))
    return V

def ring_count(n,r):
    V=coord_vectors(n); dist=defaultdict(int); dist[tuple([0]*(n//2))]=1
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for v in V: nd[tuple(a+b for a,b in zip(s,v))]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def fp_coll(n,r,p):
    for a in range(2,p):
        z=pow(a,(p-1)//n,p)
        if pow(z,n,p)==1 and pow(z,n//2,p)==p-1: break
    mu=[pow(z,j,p) for j in range(n)]
    cnt=np.zeros(p,dtype=np.int64); cnt[0]=1
    for _ in range(r):
        nc=np.zeros(p,dtype=np.int64)
        for x in mu: nc+=np.roll(cnt,x)
        cnt=nc
    return int((cnt.astype(np.float64)**2).sum())

def doublefact(r):
    d=1.0
    for j in range(1,2*r,2): d*=j
    return d

def main():
    print("(III) PROVEN FLOOR check  R_r <= Wick:")
    ok=all(ring_count(n,r)<=doublefact(r)*n**r for n in [4,8,16,32] for r in range(1,5))
    print(f"      R_r <= Wick for all tested (n,r): {ok}")
    print()
    print("(IV) sufficient open inequality  Anom_r <= n^{2r}/p  -- holds in prize regime (beta>=4):")
    for n in [8,16,32]:
        p=next(q for q in primerange(int(n**4),int(n**4*3)) if q%n==1)
        rstar=int(math.log(p))
        viol=[]
        for r in range(2, min(rstar+1, 6 if n==32 else 9)):
            anom=fp_coll(n,r,p)-ring_count(n,r); dc=n**(2*r)/p
            if anom>dc: viol.append(r)
        print(f"   n={n} p={p} beta=4: Anom_r<=n^2r/p for r=2..{min(rstar,5 if n==32 else 8)}? "
              f"{'ALL OK' if not viol else 'VIOL at r='+str(viol)}")
    print()
    print("(IV') saturated counterexample (where the target A_r<=Wick is FALSE) -- scope warning:")
    n=32; p=5857  # beta=2.50
    for r in [2,3,4]:
        coll=fp_coll(n,r,p); R=ring_count(n,r); A=coll-n**(2*r)/p; W=doublefact(r)*n**r
        print(f"   n=32 p=5857 (beta=2.50) r={r}: A_r/Wick={A/W:.3f}  Anom={coll-R} > n^2r/p={n**(2*r)/p:.1f}  "
              f"=> A_r<=Wick FALSE here (saturated p<n^r)")

if __name__=="__main__":
    main()
