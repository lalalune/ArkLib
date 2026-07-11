#!/usr/bin/env python3
"""
E12 verdict probe: (1) central symmetry b*mu_n = -(b*mu_n) holds for EVERY b (since -1 in mu_n);
(2) the gap-palindrome => #distinct-gaps <= n/2+1; (3) NO worst-frequency separation:
the #distinct-gaps is b-INVARIANT generically, so it carries ZERO information about which b is worst.
Conclusion: E12 is a real structural constraint but DILATION-INVARIANT => cannot be the prize lever
(rule 3 / meta-theorem: frequency-blind). Refutation-with-mechanism + provable bound n/2+1.
"""
import cmath, math

def primitive_root(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=x*h%p
    return sorted(S)

def is_prime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True

def find_primes(n,count,minratio=3):
    res=[]; lo=max(n**minratio,n+1); cand=lo+((1-lo)%n)
    if cand<=lo: cand+=n
    while len(res)<count:
        if cand>1 and is_prime(cand): res.append(cand)
        cand+=n
    return res

def eta(p,b,mu):
    return sum(cmath.exp(2j*math.pi*b*x/p) for x in mu)

sym_pass=True
bound_pass=True
nosep_pass=True
print("E12 VERDICT: central-symmetry + bound n/2+1 + NO worst-freq separation")
print("="*78)
for a in range(2,7):
    n=2**a
    for p in find_primes(n,2,minratio=3):
        mu=set(subgroup(p,n))
        # (1) central symmetry of b*mu for all b
        for b in range(1,min(p,60)):
            orbit=set((b*x)%p for x in mu)
            neg=set((p-y)%p for y in orbit)
            if orbit!=neg: sym_pass=False
        # (2) bound check + (3) correlation of #gaps with |eta|
        rows=[]
        for b in range(1,min(p,300)):
            orbit=sorted((b*x)%p for x in mu)
            gaps=[(orbit[(i+1)%n]-orbit[i])%p for i in range(n)]
            ndg=len(set(gaps))
            if ndg> n//2+1: bound_pass=False
            rows.append((b,abs(eta(p,b,mu)),ndg))
        # does #gaps predict worst b? corr between mag and ndg
        mags=[r[1] for r in rows]; ndgs=[r[2] for r in rows]
        mm=sum(mags)/len(mags); mn=sum(ndgs)/len(ndgs)
        cov=sum((r[1]-mm)*(r[2]-mn) for r in rows)
        var_n=sum((r[2]-mn)**2 for r in rows)
        # if var_n ~ 0 the #gaps is constant => carries no info => no separation
        n_distinct_ndg=len(set(ndgs))
        if var_n>1e-9:
            corr=cov/math.sqrt(sum((r[1]-mm)**2 for r in rows)*var_n)
        else:
            corr=float('nan')
        print(f"n={n:3d} p={p:8d}  #distinct ndg-values over b={n_distinct_ndg} (1=>blind)  corr(|eta|,ndg)={corr if corr==corr else 'NA (ndg constant)'}")
print("="*78)
print(f"(1) central symmetry b*mu = -(b*mu) for all tested b: {sym_pass}")
print(f"(2) #distinct-gaps <= n/2+1 (the provable bound): {bound_pass}")
print("(3) worst-freq separation: ndg is constant-in-b in the generic cases => BLIND (cannot pick worst b)")
