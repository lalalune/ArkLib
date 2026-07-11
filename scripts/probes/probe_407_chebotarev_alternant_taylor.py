#!/usr/bin/env python3
"""
Probe the n=4 instance of the Chebotarev generalized-Vandermonde alternant crux.

Setup (mirroring _ChebotarevAlternantThree): rows ri, cols ci : Fin n -> Z/p injective.
minorExp e_{i,j} is a NAT; (e_{i,j} mod p) = -(ci_j * ri_i).  The alternant (degree-n
Taylor-at-1 coeff of the minor poly) equals
    alternant = sum_{sigma in S_n} sign(sigma) * C(s_sigma, n),  s_sigma = sum_i e_{i,sigma(i)}.
We want: is alternantModP = c_n * V_r * V_c  for a UNIVERSAL constant c_n mod p?
  V_r = prod_{i<j}(ri_i - ri_j),  V_c = prod_{i<j}(ci_i - ci_j).
For n=3 the in-tree result is 6*alt = -3 Vr Vc  => alt = -1/2 Vr Vc, c_3 = -1/2.

We compute, for n=4, over several primes, the ratio alt/(Vr*Vc) mod p across MANY
injective (ri,ci) and check it is constant = c_4. Then identify c_4 as a rational.

The actual e_{i,j} NAT value doesn't matter mod p beyond e ≡ -(ci_j ri_i); but C(s,n) is a
NAT binomial of the NAT s, then cast. Since n!*C(s,n) = s(s-1)...(s-n+1) is a poly identity,
n! * altModP = sum_sigma sign * prod_{t=0}^{n-1}(s_sigma - t)  mod p, where s_sigma mod p is
known (= sum_i -(ci_{sigma i} ri_i)). BUT s_sigma as a NAT also matters for C unless we use the
descending-factorial form. The in-tree proof uses n!*C(s,n) = descending factorial, valid as a
ZMod identity ONLY through the cast of the NAT s. Since the descending factorial is a polynomial
in s, and we know s mod p, we can compute n!*altModP purely from s mod p. So:
    n! * altModP = sum_sigma sign(sigma) * prod_{t=0}^{n-1} ( (s_sigma mod p) - t )   (mod p)
with (s_sigma mod p) = sum_i ( -(ci_{sigma i} * ri_i) ) mod p.
We compute c_n = altModP/(Vr Vc) = [ (1/n!) sum_sigma sign prod_t (S_sigma - t) ] / (Vr Vc).
"""
import itertools, random
from math import comb
from fractions import Fraction

def is_prime(m):
    if m<2: return False
    d=2
    while d*d<=m:
        if m%d==0: return False
        d+=1
    return True

def descfact(s, n, p):
    r=1
    for t in range(n):
        r=(r*((s - t) % p))%p
    return r

def Vandermonde(v, p):
    n=len(v); r=1
    for i in range(n):
        for j in range(i+1,n):
            r=(r*((v[i]-v[j])%p))%p
    return r

def alt_modp(ri, ci, n, p):
    # n! * altModP = sum_sigma sign * descfact(S_sigma, n, p)
    total=0
    for sigma in itertools.permutations(range(n)):
        # sign
        sign=1
        for a in range(n):
            for b in range(a+1,n):
                if sigma[a]>sigma[b]: sign=-sign
        S=0
        for i in range(n):
            S=(S - (ci[sigma[i]]*ri[i])) % p   # s_sigma mod p
        total=(total + sign*descfact(S, n, p))%p
    # divide by n!
    nf=1
    for t in range(1,n+1): nf*=t
    return (total * pow(nf % p, p-2, p)) % p

def run(n, p, trials=200, seed=0):
    random.seed(seed)
    ratios=set()
    nonzero_checks=0
    for _ in range(trials):
        # injective ri, ci in Z/p
        if p < n: continue
        ri=random.sample(range(p), n)
        ci=random.sample(range(p), n)
        Vr=Vandermonde(ri,p); Vc=Vandermonde(ci,p)
        if Vr==0 or Vc==0: continue
        alt=alt_modp(ri,ci,n,p)
        ratio=(alt * pow((Vr*Vc)%p, p-2, p))%p
        ratios.add(ratio)
        nonzero_checks+=1
    return ratios, nonzero_checks

def as_rational(c, p, maxden=24):
    # find small rational a/b with a*inv(b) == c mod p
    for b in range(1, maxden+1):
        for a in range(-maxden, maxden+1):
            if (a * pow(b, p-2, p) - c) % p == 0:
                return Fraction(a, b)
    return None

if __name__=="__main__":
    print("n=3 sanity (expect c_3 = -1/2):")
    for p in (5,7,11,13):
        r,nc=run(3,p,trials=80,seed=p)
        cs=[as_rational(c,p) for c in r]
        print(f"  p={p}: ratios mod p={sorted(r)} -> rationals {sorted(set(str(x) for x in cs))} ({nc} checks)")
    print("n=4 (find c_4):")
    for p in (7,11,13,17,19,23):
        r,nc=run(4,p,trials=200,seed=p)
        cs=[as_rational(c,p) for c in r]
        print(f"  p={p}: #distinct ratios={len(r)} -> rationals {sorted(set(str(x) for x in cs))} ({nc} checks)")
    print("n=5 (find c_5):")
    for p in (7,11,13,17,19,23,29):
        r,nc=run(5,p,trials=200,seed=p+1)
        cs=[as_rational(c,p) for c in r]
        print(f"  p={p}: #distinct ratios={len(r)} -> rationals {sorted(set(str(x) for x in cs))} ({nc} checks)")
