#!/usr/bin/env python3
"""
Door-(iv) Lane 1 sweep 5 — is the period MARGINAL Gaussian to 4th order, or is there a
heavy-tail EXCESS where a higher-order door-(iv) functional could grip?

My white-field sweep (b383e13d5) killed the 2nd-order joint structure. The chain pointer: any door-(iv)
crack must live in a HIGHER-ORDER / nonlinear functional. The first such functional is the complex
4th moment of the period marginal:
    K4 = E_b[ |eta_b|^4 ] / ( E_b[ |eta_b|^2 ] )^2
For a complex GAUSSIAN eta (the EVT/door-iii model), K4 = 2 EXACTLY (E|Z|^4 = 2(E|Z|^2)^2).
  - K4 -> 2  => the marginal is Gaussian to 4th order; the sup is the Gaussian-EVT value (door iii, dead)
              and NO marginal heavy tail exists for a door-(iv) functional to exploit.
  - K4 > 2   => heavy tail / non-Gaussian marginal; the EXCESS (K4-2) is the candidate structure.

This is DISTINCT from the refuted additive-energy E_4 route (§6): that is the 4-POINT additive sum
Sigma_{b+b'=b''+b'''}, an energy object. K4 is the ONE-POINT marginal kurtosis of the period field, a
heavy-tail diagnostic, not an additive-energy bound. Also report the real-part kurtosis and the ratio
E|eta|^6 / (E|eta|^2)^3 (=6 for complex Gaussian) for a second-order check on Gaussianity.

EXACT complex arithmetic over coset reps, proper mu_n, p>>n^3, multiple primes incl Fermat, never n=q-1.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
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

def find_prime(n,beta):
    t=int(round(n**beta)); k0=max(2,t//n)
    for dk in range(0,400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n and is_prime(p): return p
    return None

def subgroup(p,n):
    pm1=p-1; f={}; m=pm1; d=2
    while d*d<=m:
        while m%d==0: f[d]=1; m//=d
        d+=1
    if m>1: f[m]=1
    def isg(g): return all(pow(g,pm1//q,p)!=1 for q in f)
    g=2
    while not isg(g): g+=1
    h=pow(g,pm1//n,p); mu=[]; c=1
    for _ in range(n): mu.append(c); c=c*h%p
    return mu,g

def eta_c(b,mu,p):
    return sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in mu)

def main():
    print("=== complex 4th/6th-moment Gaussianity of the period marginal ===")
    print(f"{'n':>4} {'beta':>4} {'p':>11} {'N':>7} {'E|e|2/n':>8} {'K4':>7} {'K4-2':>7} "
          f"{'K6':>7} {'K6/6':>6}")
    for n,beta in [(16,4.0),(32,4.0),(64,4.0),(128,4.0),(16,4.5),(32,4.5),(64,4.5),(16,5.0)]:
        p=find_prime(n,beta)
        if p is None: continue
        mu,g=subgroup(p,n)
        N=(p-1)//n; cap=min(N,60000)
        cur=1; m2=0.0; m4=0.0; m6=0.0
        for j in range(cap):
            a=abs(eta_c(cur,mu,p)); a2=a*a
            m2+=a2; m4+=a2*a2; m6+=a2*a2*a2
            cur=cur*g%p
        m2/=cap; m4/=cap; m6/=cap
        K4=m4/(m2*m2); K6=m6/(m2**3)
        print(f"{n:>4} {beta:>4} {p:>11} {N:>7} {m2/n:>8.4f} {K4:>7.4f} {K4-2:>7.4f} "
              f"{K6:>7.3f} {K6/6:>6.3f}")
    print("\n(complex Gaussian baseline: E|e|2/n=1, K4=2.0, K6=6.0. K4-2>0 => heavy tail / non-Gaussian.)")

if __name__=="__main__":
    main()
