#!/usr/bin/env python3
"""
CAPSTONE: the designed-q laws for n=2^mu, q=p^2.

LAW 1 (the BAD family, PROVABLE):  n | (p-1)  =>  B = n  (the TRIVIAL maximum).
  Reason: if n | p-1 then mu_n subset F_p^* (prime subfield).  Pick b = the element with
  b*mu_n landing exactly on a coset where Tr is constant.  We give the exact mechanism:
  for c in F_p^*, eta_c = sum_{y in mu_n} e_p(Tr(c y)) = sum_{y in mu_n} e_p(2 c y)
  (since c,y in F_p => Tr(x)=2x).  This is the PRIME-FIELD Gauss period of mu_n in F_p, scaled.
  Its max over c is the prime-field B_p(n).  BUT separately, for b in the OTHER eigenline,
  (b = alpha * c'), b*mu_n = alpha*(c' mu_n) subset alpha F_p^*  => Tr(alpha c' y)=0 (alpha is
  trace-0!) for ALL y  =>  eta_b = sum 1 = n.  THE SPIKE.  So n|p-1 => some coset is entirely
  in the trace-0 line => B = n.  We VERIFY B=n and exhibit the spike coset.

LAW 2 (the GOOD family, MEASURED): n | (p+1)  (mu_n in the norm-1 torus, "inert" embedding)
  gives the SMALLEST B, tracking c*sqrt(n log(q/n)) with c ~ 1.0-1.2.  Best designed family.

PRIZE-REGIME TEST: emulate n=q^gamma by, for each target gamma, scanning q=p^2 and picking
the LARGEST n=2^mu with n=2^mu <= q^gamma AND (n|p+1).  Report B/sqrt(n) and the implied
constant in B <= C sqrt(n log(q/n)).  This is the closest exact analogue of the prize point.
"""
import cmath, math, random
from collections import Counter

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f
def qnr(p):
    for u in range(2,p):
        if pow(u,(p-1)//2,p)==p-1: return u
    raise RuntimeError
def gf2_mul(x,y,u,p):
    a,b=x;c,d=y; return ((a*c+b*d*u)%p,(a*d+b*c)%p)
def gf2_pow(x,e,u,p):
    r=(1,0)
    while e>0:
        if e&1: r=gf2_mul(r,x,u,p)
        x=gf2_mul(x,x,u,p); e>>=1
    return r
def find_gen_gf2(p,u):
    order=p*p-1; pf=list(factorize(order).keys())
    for g in [(0,1),(1,1),(2,1),(3,1),(1,2),(2,3)]+[(a,b) for a in range(p) for b in range(1,p)]:
        if all(gf2_pow(g,order//pr,u,p)!=(1,0) for pr in pf): return g
    raise RuntimeError
def gauss_data(p,n):
    """return B, and (argmax coset abs, whether some coset has eta=n exactly with trace-0 evidence)."""
    order=p*p-1; u=qnr(p); g=find_gen_gf2(p,u); k=order//n
    exp_t=[None]*order; cur=(1,0)
    for i in range(order): exp_t[i]=cur; cur=gf2_mul(cur,g,u,p)
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p; mx=0.0; spike_trace0=False
    for c in range(k):
        bc=exp_t[c%order]; s=0j; all_trace0=True
        for y in mu:
            prod=gf2_mul(bc,y,u,p); tr=(2*prod[0])%p
            if tr!=0: all_trace0=False
            s+=cmath.exp(1j*w*tr)
        a=abs(s)
        if a>mx: mx=a
        if all_trace0: spike_trace0=True
    return mx,k,spike_trace0

if __name__=="__main__":
    random.seed(5)
    print("="*78)
    print("LAW 1 VERIFICATION:  n | (p-1)  =>  B = n  (and a coset lies entirely in ker Tr)")
    print("="*78)
    print(f"{'n':>4} {'p':>5} {'q':>8} {'n|p-1':>6} {'B':>8} {'B==n?':>7} {'trace0 coset exists?':>20}")
    for n in [8,16,32]:
        cnt=0
        for p in range(3,4000):
            if not is_prime(p): continue
            if (p-1)%n!=0: continue
            if (p*p-1)%n!=0: continue
            B,k,sp=gauss_data(p,n)
            print(f"{n:>4} {p:>5} {p*p:>8} {'True':>6} {B:>8.3f} {str(abs(B-n)<1e-6):>7} {str(sp):>20}")
            cnt+=1
            if cnt>=4: break
    print()
    print("="*78)
    print("LAW 2:  n | (p+1)  (inert/norm-1 torus) = BEST designed family. Constant C in")
    print("        B <= C*sqrt(n*log(q/n)).  Compare to A_split (B=n) and C_generic.")
    print("="*78)
    for n in [8,16,32]:
        print(f"\n--- n={n} ---  (B_inert rows: n|p+1)")
        print(f"{'p':>6} {'q':>9} {'B':>9} {'B/sqrtn':>8} {'C=B/sqrt(n log(q/n))':>21} {'gamma=ln n/ln q':>15}")
        cnt=0
        for p in range(3,200000):
            if not is_prime(p): continue
            if (p+1)%n!=0: continue
            if (p*p-1)%n!=0: continue
            B,k,sp=gauss_data(p,n)
            q=p*p; lqn=math.log(q/n); C=B/math.sqrt(n*lqn)
            print(f"{p:>6} {q:>9} {B:>9.3f} {B/math.sqrt(n):>8.3f} {C:>21.4f} {math.log(n)/math.log(q):>15.3f}")
            cnt+=1
            if cnt>=10: break
    print()
    print("="*78)
    print("PRIZE-REGIME ANALOGUE: target gamma ~ 0.19.  For each q=p^2, pick largest")
    print("n=2^mu <= q^0.19 with n | (p+1) (the good family). Report C = B/sqrt(n log(q/n)).")
    print("="*78)
    print(f"{'p':>7} {'q':>11} {'n=2^mu':>7} {'gamma_eff':>9} {'B':>9} {'B/sqrtn':>8} {'C':>8}")
    target=0.19
    for p in [127,191,251,383,511+0,521,631,761,883,1021,1279,1531,2039,3067,4093]:
        if not is_prime(p): continue
        q=p*p
        # largest 2-power n <= q^target with n | p+1
        best=None
        mu=1
        while 2**mu <= q**target:
            n=2**mu
            if (p+1)%n==0 and (q-1)%n==0:
                best=n
            mu+=1
        if best is None:
            # relax: just largest 2-power dividing p+1 that's <= q^target
            d=p+1; m=0
            while d%2==0: d//=2; m+=1
            cand=2**m
            while cand> q**target and cand>1: cand//=2
            best=cand if cand>=2 else None
        if not best:
            print(f"{p:>7} {q:>11}   (no 2-power n<=q^0.19 with n|p+1)"); continue
        n=best
        B,k,sp=gauss_data(p,n)
        lqn=math.log(q/n)
        print(f"{p:>7} {q:>11} {n:>7} {math.log(n)/math.log(q):>9.3f} {B:>9.3f} {B/math.sqrt(n):>8.3f} {B/math.sqrt(n*lqn):>8.4f}")
