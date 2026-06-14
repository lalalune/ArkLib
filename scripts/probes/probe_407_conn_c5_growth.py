#!/usr/bin/env python3
"""
#407 C5 — confirm the telescoped closures give the TRIVIAL (n^{2k}, Johnson) growth, not Wick (n^k).

The only closures that telescope (drop A^chi>=0, bound interior M_{i,k-i}) are:
   Young:  A_k(n) <= 4^k A_k(n/2)   =>  A_k(2^mu) <= 4^{k(mu-1)} A_k(mu_2) = 4^{k(mu-1)} C(2k,k).
With n=2^mu, 4^{k(mu-1)} = (2^mu)^{2k}/4^k = n^{2k}/4^k. So Young gives A_k(n) <~ n^{2k} (TRIVIAL:
this is the same as just |eta_b|^2 <= n^2 plugged in, i.e. the second-moment/Johnson ceiling, NO
sqrt-cancellation). Wick needs n^k. The GAP factor is n^k -- exactly the sqrt-cancellation the
prize is about. So the telescoping LOSES a factor of n^k = the entire content.

This probe makes the loss explicit: per-level the EXACT ratio A_k(n)/A_k(n/2) is what we need to be
~2^k (to give n^k after mu levels), but Young forces <=4^k, and the TRUE ratio: measure it.

KEY DIAGNOSIS (the alignment obstruction, moment version):
   needed per-level ratio  A_k(n)/A_k(n/2) ~ 2^k   (Wick: (2k-1)!!n^k / (2k-1)!!(n/2)^k = 2^k).
   trivial per-level ratio  ~ 4^k  (Young upper bound).
   So the question is whether the recursion can prove the ratio is 2^k not 4^k.
   The factor-2 gap PER LEVEL is EXACTLY the L^infty 'M(n)^2 vs 2 M(n/2)^2' question
   (KB: ratios 3.58/3.10/2.51 -- between 2 and 4, NOT provably <=2 by the recursion).
"""
import cmath, math
from sympy import primitive_root as pr
from math import comb

def step(t,m,p):
    S=[]; x=1
    for _ in range(m): S.append(x); x=(x*t)%p
    return S
def eta_real(c,S,p):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((c*x)%p)) for x in S).real
def df(m):
    r=1
    for j in range(1,m+1,2): r*=j
    return r
def Ak(n,p,kmax):
    g=int(pr(p)); t=pow(g,(p-1)//n,p); S=step(t,n,p)
    a=[0.0]*(kmax+1)
    for b in range(1,p):
        e=eta_real(b,S,p); e2=e*e; pw=1.0
        for k in range(1,kmax+1): pw*=e2; a[k]+=pw
    return [a[k]/p for k in range(kmax+1)]

def main():
    kmax=4
    # use a deep-tower prime so we can climb mu=1..several at FIXED p (non-saturated)
    # need p ≡ 1 mod 2^mu_max. pick p with large 2-adic valuation.
    for p in [40961, 65537, 786433]:   # 40961=5*2^13+1, 65537=2^16+1, 786433=3*2^18+1
        v2 = 0; m=p-1
        while m%2==0: m//=2; v2+=1
        mu_max = min(v2, 9)
        print(f"\n{'='*100}\np={p}  (v2(p-1)={v2}, climbing mu=1..{mu_max})")
        print(f"  PER-LEVEL RATIO A_k(2^mu)/A_k(2^(mu-1)):  Wick-needed=2^k, Young-allows<=4^k")
        prev=None
        for mu in range(1,mu_max+1):
            n=2**mu
            a=Ak(n,p,kmax)
            if prev is not None:
                ratios=[a[k]/prev[k] if prev[k] else float('nan') for k in range(1,kmax+1)]
                need=[2**k for k in range(1,kmax+1)]
                triv=[4**k for k in range(1,kmax+1)]
                print(f"  mu={mu:2d} n={n:4d}: ratios={['%.2f'%r for r in ratios]}  "
                      f"(need 2^k={need}, Young<=4^k={triv})")
            prev=a
        # final: A_k(n)/Wick and A_k(n)/(n^{2k}/4^k) [the Young/trivial target]
        n=2**mu_max; a=Ak(n,p,kmax)
        print(f"  FINAL n={n}: " + "  ".join(
            f"k{k}: A_k/Wick={a[k]/(df(2*k-1)*n**k):.3f}, A_k/(n^2k/4^k)={a[k]/((n**(2*k))/4**k):.4f}"
            for k in range(1,kmax+1)))

if __name__=="__main__":
    main()
