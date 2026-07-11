#!/usr/bin/env python3
"""
probe_c71_binomial_incidence_sharp.py  (#444, #389)

LANE: SHARPNESS of the C71 binomial mu_n-incidence bound. C71BinomialIncidenceGcd proves
    #{x in mu_n : x^i - c x^j = 0}  <=  gcd(|i-j|, n).
This probe confirms that bound is ATTAINED (a worst-case witness exists): the direction
    f = X^d - 1      (c = 1, target gamma = 1, the worst case from the attainment criterion)
has EXACTLY gcd(d, n) roots in mu_n, namely the subgroup mu_{gcd(d,n)} <= mu_n. So the gcd
incidence bound is the SHARP worst-case count over the binomial strata, not merely an upper bound.

EXACT F_p, thin mu_n = order-n subgroup, n = 2^a a in 2..5, p == 1 mod n, (p-1)/n >= 2
(PROPER subgroup, NEVER n = q-1), primes incl p > n^3 and Fermat 257/65537.
"""
import sys

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def gcd(a,b):
    while b: a,b = b,a%b
    return a

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def primitive_root(p):
    if p==2: return 1
    phi=p-1; fs=factorize(phi)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fs): return g
    raise RuntimeError

def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def primes_one_mod_n(n,count,min_p):
    out=[]; p=n*(max(1,min_p//n))+1
    while p<min_p: p+=n
    while len(out)<count:
        if p>1 and is_prime(p) and p%n==1: out.append(p)
        p+=n
    return out

def run():
    total=okSharp=okSubgroup=0; fails=[]
    for a in range(2,6):
        n=2**a
        ps=primes_one_mod_n(n,6,2*n+1)+primes_one_mod_n(n,2,n**3+1)
        for fp in (257,65537):
            if fp%n==1: ps.append(fp)
        ps=sorted(set(ps))
        for p in ps:
            if (p-1)//n<2: continue
            S=mu_n(p,n); Sset=set(S)
            for d in range(1,n+1):
                g=gcd(d,n)
                # witness f = X^d - 1: roots in mu_n
                roots=[x for x in S if pow(x,d,p)==1]
                total+=1
                # (1) sharpness: exactly gcd(d,n) roots
                if len(roots)==g: okSharp+=1
                else: fails.append((n,p,d,len(roots),g))
                # (2) those roots ARE the order-g subgroup mu_g <= mu_n
                # check: each root r satisfies r^g == 1, and they're exactly g of them
                if all(pow(r,g,p)==1 for r in roots) and len(set(roots))==g:
                    okSubgroup+=1
    print(f"(1) witness X^d-1 has EXACTLY gcd(d,n) roots in mu_n: {okSharp}/{total} OK")
    print(f"(2) roots == subgroup mu_gcd(d,n) <= mu_n:             {okSubgroup}/{total} OK")
    if fails: print("FAILS:", fails[:12])
    v=(not fails) and okSubgroup==total
    print("VERDICT:", "SHARP — gcd bound ATTAINED" if v else "VIOLATIONS")
    return 0 if v else 1

if __name__=="__main__":
    sys.exit(run())
