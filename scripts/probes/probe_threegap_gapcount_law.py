#!/usr/bin/env python3
"""
E12 follow-up: PIN the exact gap-count law and its dilation-invariance + mechanism.
Claim to test:  #distinct-gaps(b*mu_n mod p) = n/2 + 1  for EVERY b != 0, all prize-regime (n,p).
Mechanism hypothesis: mu_n = -mu_n (contains -1 for n>=2, since n even => the order-2 element
-1 is in any even-order subgroup). So the position multiset is symmetric x <-> p-x, forcing the
gap multiset to be a palindrome => distinct gaps <= n/2 + 1, and genericity => equality.
"""
import math

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
    res=[]; lo=max(n**minratio,n+1)
    cand=lo+((1-lo)%n)
    if cand<=lo: cand+=n
    while len(res)<count:
        if cand>1 and is_prime(cand): res.append(cand)
        cand+=n
    return res

def ndg(positions,p):
    s=sorted(positions); gaps=[]
    for i in range(len(s)):
        gaps.append((s[(i+1)%len(s)]-s[i])%p)
    return len(set(gaps))

print("PIN: #distinct-gaps(b*mu_n) == n/2+1 for ALL b!=0, + mech (-1 in mu_n => palindrome gaps)")
print("="*78)
allpass=True
neg1pass=True
for a in range(2,8):
    n=2**a
    for p in find_primes(n,3,minratio=3):
        mu=subgroup(p,n)
        assert len(mu)==n<p-1
        has_neg1 = ((p-1) in mu)
        if not has_neg1: neg1pass=False
        bs = range(1,p) if n<=32 else [1,2,3,5,7,11,13,p-1,p-2,(p-1)//2 or 1,17,19,23,29,31,37]
        vals=set()
        for b in bs:
            if b%p==0: continue
            orbit=[(b*x)%p for x in mu]
            vals.add(ndg(orbit,p))
        expected = n//2+1
        ok = (vals == {expected})
        if not ok: allpass=False
        print(f"n={n:4d} p={p:8d}  -1 in mu_n: {has_neg1}  #gaps set over b: {sorted(vals)}  exp {expected}  {'OK' if ok else 'FAIL'}")
print("="*78)
print(f"ALL b give exactly n/2+1 distinct gaps: {allpass}")
print(f"-1 always in mu_n (palindrome mechanism): {neg1pass}")
