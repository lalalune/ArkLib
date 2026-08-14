#!/usr/bin/env python3
"""
A6 CRUX — the order-of-limits question that decides the horn.

Observed (probe_a6_even_moment_growth): at FIXED n, the normalized period
measure nu_{n,p} converges in moments to a p-INDEPENDENT limit; the edge
E_n(p) = M(mu_n)/sqrt(n) appears to SATURATE to a constant E_n as p -> inf.

IF lim_{p->inf} M(mu_n)/sqrt(n) = E_n < inf for each fixed n, then for fixed n
M is BELOW Johnson's sqrt(n log(p/n)) for large p (since log(p/n)->inf).
THAT WOULD BE A CRACK -- but ONLY if it survives the right regime.

Two things to nail, skeptically:
 (1) Confirm E_n(p) genuinely SATURATES (not slowly diverging) at fixed n, by
     pushing p over MANY decades and watching M (not M/sqrt(n*log) which hides it).
 (2) Measure how the SATURATED limit E_n grows with n.  The prize regime has
     n -> inf (n=2^mu, constant rate n ~ q^c).  If E_n ~ c*sqrt(log n) or grows
     without bound, then when n and p grow together M ~ sqrt(n log) = Johnson and
     there is NO crack.  If E_n -> bounded constant as n->inf, that IS the floor.

KNOWN MATH CHECK: the Gauss-period sup-norm for FIXED n as p->inf is a classical
object.  For n fixed, eta_i / sqrt(n)... actually the periods are sums of n
n-th-power Gauss sums; the max period for fixed n, p->inf is governed by the
LARGEST root of the fixed period polynomial family, which by Weil/Deligne for
the associated curve is O(sqrt(n))?  No -- for FIXED small n the periods are
explicit (n=2: eta=(-1±sqrt(p*))/2 ~ sqrt(p)!!).  WAIT: for n=2 (quadratic
periods) the max period is ~sqrt(p), NOT O(1)*sqrt(2).  Re-examine: our mu_n is
the order-n SUBGROUP; n=2 subgroup = {1,-1}; periods of the order-(p-1)/2 ...
NO.  Careful: M(mu_n)=max_b|sum_{x in mu_n} e_p(bx)|, mu_n has n elements.  For
n=2: sum = e_p(b)+e_p(-b)=2cos(2pi b/p), max over b = 2cos(2pi/p) ~ 2 = n.  So
E_2 = M/sqrt(2) = sqrt(2).  These are SMALL periods (n terms), NOT the big
(p-1)/2-term quadratic period.  Good -- so E_n bounded is plausible & is the
real question.
"""
import math
import numpy as np
from sympy import isprime

def primitive_root(p):
    phi=p-1; fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def Mval(p,n):
    """max_{b!=0} |sum_{x in mu_n} e_p(b x)|, mu_n the order-n subgroup."""
    g=primitive_root(p)
    gm=pow(g,(p-1)//n,p)
    sub=[]; cur=1
    for _ in range(n): sub.append(cur); cur=cur*gm%p
    sub=np.array(sub,dtype=np.int64)
    m=(p-1)//n
    # the m distinct period values arise from b in coset reps g^i, i=0..m-1.
    # But M = max over ALL b!=0; equivalently max over i of |sum cos,sin|.
    # For large m this is expensive; instead sample b over all residues in chunks?
    # Cheapest exact: iterate i=0..m-1 with b=g^i. m can be ~1e7 -> too slow in py.
    # Use vectorized: for ALL b in 1..p-1 at once is p*n memory -> too big.
    # Compromise: compute periods via the bucket method (sum over cosets), O(p).
    N=p-1; B=int(math.isqrt(N))+1
    low=[1]*B; cur=1
    for b in range(B): low[b]=cur; cur=cur*g%p
    gB=cur; A=(N+B-1)//B; low=np.array(low,dtype=object)
    eta=np.zeros(m); twop=2.0*math.pi/p; cur=1
    for a in range(A):
        b0=a*B; bc=min(B,N-b0)
        if bc<=0: break
        res=((cur*low[:bc])%p).astype(np.float64)
        np.add.at(eta,np.arange(b0,b0+bc)%m,np.cos(twop*res))
        cur=cur*gB%p
    return float(np.max(np.abs(eta)))

def find_primes(n,count,pmin):
    res=[]; t=pmin//n+1
    while len(res)<count:
        p=1+n*t
        if isprime(p): res.append(p)
        t+=1
    return res

if __name__=="__main__":
    print("=== A6 CRUX: (1) fixed-n saturation of E_n(p)=M/sqrt(n) over many decades ===\n")
    for mu in [3,4,5]:
        n=2**mu; sn=math.sqrt(n)
        print(f"--- n={n} (sqrt n={sn:.3f}) ---")
        prev=None
        for c in [50,300,2000,12000,80000,500000]:
            pmin=min(c*n**3, 4*10**7)
            for p in find_primes(n,1,pmin):
                M=Mval(p,n); En=M/sn
                d="" if prev is None else f"  dE={En-prev:+.4f}"
                print(f"   p={p:>10} p/n^3={p/n**3:8.0f}  M={M:8.4f}  E_n={En:7.4f}"
                      f"  (Johnson sqrt(log)={math.sqrt(math.log(p/n)):.3f}){d}")
                prev=En
        print()
    print("=== (2) how does the (near-)saturated E_n grow with n? (largest p each) ===")
    print("Compare E_n growth to sqrt(log n) and to constant.\n")
    res=[]
    for mu in [2,3,4,5,6,7,8]:
        n=2**mu
        pmin=min(2000*n**3, 4*10**7)
        for p in find_primes(n,1,pmin):
            M=Mval(p,n); En=M/math.sqrt(n)
            res.append((n,En,p))
            print(f"   n={n:4d} p={p:>10} p/n^3={p/n**3:7.0f}  E_n={En:7.4f}"
                  f"  E_n/sqrt(log n)={En/math.sqrt(math.log(n)):.4f}"
                  f"  E_n/sqrt(log(p/n))={En/math.sqrt(math.log(p/n)):.4f}")
    print()
    print("HORN: if E_n keeps growing ~sqrt(log(p/n)) it's Johnson. If E_n saturates")
    print("to an absolute constant as n->inf, that is the floor (a crack).")
