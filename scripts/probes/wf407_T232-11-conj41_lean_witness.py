#!/usr/bin/env python3
"""
wf407_T232-11-conj41_lean_witness.py
====================================
Extract an EXPLICIT small-prime witness of the mu_n refutation of the INTENDED
(fixed-syndrome) form of Conjecture 41, suitable for a Lean `decide` brick.

We want the SMALLEST prime p and n | p-1 with n >= 28 (so n/4-1 >= 6 > ceiling 5)
where a family of >= 6 genuine weight-6 supports of mu_n shares a full (e_1,e_2,e_3)
class.  p=29 gives mu_28 = F_29^* (the whole group).  We dump:
  - the explicit support sets (as field elements of ZMod p);
  - the shared class (e_1,e_2,e_3);
  - the explicit class syndrome s (length 9) so CompatC(s,3,E_i) holds for all i;
  - a sanity-check that all are genuine and pairwise distinct.
This is the data a `conj41_mun_REFUTED` Lean brick would `decide` over `ZMod p`.
"""

import itertools
from collections import defaultdict

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d,s=n-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def nextprime(n):
    n=int(n)+1
    while not is_prime(n): n+=1
    return n

def factorize(n):
    fac={}; d=2
    while d*d<=n:
        while n%d==0: fac[d]=fac.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: fac[n]=fac.get(n,0)+1
    return fac

def primitive_root(p):
    phi=p-1; fac=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    raise RuntimeError

def mu_n(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p)%p for i in range(n)]

def esymm(E,j,p):
    if j==0: return 1
    acc=0
    for c in itertools.combinations(E,j):
        pr=1
        for x in c: pr=pr*x%p
        acc=(acc+pr)%p
    return acc

def locator_coeffs(E,p):
    co=[1]
    for a in E:
        a%=p; new=[0]*(len(co)+1)
        for i,ci in enumerate(co):
            new[i]=(new[i]-a*ci)%p; new[i+1]=(new[i+1]+ci)%p
        co=new
    return co

def err_vals_nonzero(E,p):
    El=list(E)
    for x in El:
        pr=1
        for y in El:
            if y==x: continue
            d=(x-y)%p
            if d==0: return False
            pr=pr*d%p
        if pr==0: return False
    return True

def complete_homog(class_e,c,p):
    e=[1]+[class_e[i] for i in range(c)]
    h=[1]
    for m in range(1,c+1):
        acc=0
        for i in range(1,m+1):
            sign=1 if (i-1)%2==0 else -1
            acc=(acc+sign*e[i]*h[m-i])%p
        h.append(acc%p)
    return h

def class_syndrome(class_e,w,c,p):
    N=w+c; h=complete_homog(class_e,c,p); s=[0]*N
    for t in range(c+1): s[N-1-c+t]=h[t]%p
    return s

def synd(s,N,coeffs,p):
    return sum((coeffs[j] if j<len(coeffs) else 0)*s[j] for j in range(N))%p

def syndr_value(E,r,s,N,p):
    base=locator_coeffs(E,p); coeffs=[0]*r+base
    return synd(s,N,coeffs,p)

def find_witness(p, n, w=6, c=3, need=6):
    L=mu_n(n,p)
    cls=defaultdict(list)
    for E in itertools.combinations(L,w):
        if err_vals_nonzero(E,p):
            cls[tuple(esymm(E,j,p) for j in range(1,c+1))].append(E)
    if not cls: return None
    key=max(cls,key=lambda k:len(cls[k]))
    fam=cls[key]
    if len(fam)<need: return None
    return key, fam, L

if __name__ == "__main__":
    print("Smallest-prime explicit witness for the mu_n refutation of Conjecture 41's")
    print("INTENDED (fixed-syndrome) form  (w=6, c=3, ceiling floor((2D-1)/c)=5).\n")
    # search small primes p with n=p-1>=28 (mu_n = whole group) OR n|p-1, n>=28
    found=False
    for p in [29,43,53,57,59,71,73,79,83,89,97,101,103,107,109,113]:
        if not is_prime(p): continue
        # candidate n's: divisors of p-1 that are >=28 and <= some cap (enumerable)
        ns=[d for d in range(28,min(p-1,40)+1) if (p-1)%d==0]
        for n in ns:
            res=find_witness(p,n,need=6)
            if res:
                key,fam,L=res
                N=w=6; c=3; N=9
                s=class_syndrome(key,6,3,p)
                expo={L[i]:i for i in range(n)}
                print(f"WITNESS: p={p}, n={n} (mu_n {'=F_p^*' if n==p-1 else 'subgroup'}),"
                      f" M_fixed={len(fam)} > 5")
                print(f"  shared class (e_1,e_2,e_3) = {key}")
                print(f"  class syndrome s (len 9) = {s}")
                print(f"  mu_n = {L}")
                print(f"  supports (as ZMod {p} elements) and CompatC check:")
                for E in fam[:8]:
                    ok=all(syndr_value(E,r,s,9,p)==0 for r in range(3))
                    print(f"    {sorted(E)}  (exps {sorted(expo[x] for x in E)})  "
                          f"genuine={err_vals_nonzero(E,p)} compat={ok}")
                print(f"  all {len(fam)} compatible w/ s: "
                      f"{all(all(syndr_value(E,r,s,9,p)==0 for r in range(3)) for E in fam)}")
                print(f"  all genuine: {all(err_vals_nonzero(E,p) for E in fam)}")
                print(f"  pairwise distinct: {len(set(fam))==len(fam)}")
                found=True
                break
        if found: break
    if not found:
        print("no small-prime witness found in the scanned range")
    print("\nDONE.")
