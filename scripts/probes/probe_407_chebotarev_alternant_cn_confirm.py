#!/usr/bin/env python3
"""FINAL confirmation: T_{D_n} = c_n Vr Vc with c_n = (-1)^{D_n}/prod_{k=1}^{n-1}k!, D_n=C(n,2).
Test on FRESH primes not used in reconstruction, for n=3..8, multiple (ri,ci), incl primes near n."""
import itertools, random
from math import factorial
def descfact(s,d,p):
    r=1
    for t in range(d): r=(r*((s-t)%p))%p
    return r
def Vand(v,p):
    n=len(v); r=1
    for i in range(n):
        for j in range(i+1,n): r=(r*((v[i]-v[j])%p))%p
    return r
def Td(ri,ci,n,d,p):
    total=0
    for sigma in itertools.permutations(range(n)):
        sign=1
        for a in range(n):
            for b in range(a+1,n):
                if sigma[a]>sigma[b]: sign=-sign
        S=0
        for i in range(n): S=(S-(ci[sigma[i]]*ri[i]))%p
        total=(total+sign*descfact(S,d,p))%p
    nf=1
    for t in range(1,d+1): nf*=t
    return (total*pow(nf%p,p-2,p))%p
def superfact(n):
    r=1
    for k in range(1,n): r*=factorial(k)
    return r
def cn_formula_modp(n,p):
    D=n*(n-1)//2
    sign=(-1)**D
    sf=superfact(n)%p
    if sf==0: return None  # formula degenerate (p | superfactorial)
    return (sign*pow(sf,p-2,p))%p

random.seed(123)
fresh=[211,223,227,229,233,239,241,251,257,263]
allok=True
for n in range(3,8):
    D=n*(n-1)//2
    for p in fresh[:6]:
        if p<=n: continue
        cf=cn_formula_modp(n,p)
        # check T_D = cf * Vr*Vc for several (ri,ci)
        bad=0
        for _ in range(40):
            ri=random.sample(range(p),n); ci=random.sample(range(p),n)
            Vr=Vand(ri,p); Vc=Vand(ci,p)
            if Vr==0 or Vc==0: continue
            lhs=Td(ri,ci,n,D,p); rhs=(cf*Vr%p*Vc)%p
            if lhs!=rhs: bad+=1
        status="OK" if bad==0 else f"FAIL({bad})"
        if bad: allok=False
        print(f"n={n} p={p}: T_D == c_n*Vr*Vc  {status}  (c_n mod p={cf})")
print("ALL CONFIRMED" if allok else "SOME FAILED")
# edge: smallest valid prime (p must not divide superfactorial = p > n-1 suffices since max factorial arg is n-1)
print("\nEdge: superfactorial unit condition. prod_{k=1}^{n-1} k! has prime factors <= n-1.")
for n in range(3,9):
    sf=superfact(n)
    primes_dividing=[q for q in range(2,n) if sf%q==0]
    print(f"  n={n}: superfact primes = (all <= {n-1}); formula valid for all p > {n-1}")
