import math
from itertools import combinations, product

# CONFIRM: Fermat primes have anomalously short NONZERO ideal vectors. Extend data,
# and check whether this distinguishes Fermat from ALL nearby generic primes systematically.
# Also check if the min-l1 nonzero ideal vector correlates with v2(p-1) (2-adic structure).

def is_prime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
def prim_root(n,p):
    for g in range(2,p):
        if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return g
    return None

def true_min_l1(d,p,g,wmax=8):
    gp=[pow(g,k,p) for k in range(d)]
    for w in range(2, wmax+1):
        for supp_size in range(1, min(w,d)+1):
            for supp in combinations(range(d), supp_size):
                for cut in combinations(range(1,w), supp_size-1):
                    parts=[]; prev=0
                    for c_ in cut: parts.append(c_-prev); prev=c_
                    parts.append(w-prev)
                    for signs in product([1,-1], repeat=supp_size):
                        val=sum(signs[i]*parts[i]*gp[supp[i]] for i in range(supp_size))%p
                        if val==0:
                            return w
    return None

n=16; d=8
# scan a window of primes ==1 mod n, record (p, v2(p-1), min_l1). Fermat is the v2=16 extreme.
print(f"n={n}: min-l1 of nonzero ideal vec vs 2-adic valuation v2(p-1). Larger v2 => shorter?")
print("p          v2(p-1)  min_l1")
data=[]
# include the Fermat 65537 (v2=16) and a spread of generic primes
cands=[65537]
p=257
while p < 8000:
    if is_prime(p) and p%n==1: cands.append(p)
    p+=1
import random
random.seed(1)
sample=[65537]+sorted(random.sample([c for c in cands if c!=65537], 12))
for p in sorted(set(sample)):
    g=prim_root(n,p)
    if g is None: continue
    v2=0; m=p-1
    while m%2==0: v2+=1; m//=2
    w=true_min_l1(d,p,g,wmax=7)
    print(f"{p:<10} {v2:<8} {w}")
