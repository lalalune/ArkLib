# Among PRIZE primes p == 1 mod n (n=2^m), which are "bad" (divide SOME weight-4 antipodal-free
# norm)? Measure the density. This is the wf-C1 effective-Chebotarev object. A bad prime p (with
# ord_n(p)=1, i.e. p==1 mod n) means there exist 4 antipodal-free n-th roots in F_p summing to 0.
# Equivalently: the weight-4 "spurious vanishing" subset exists in F_p directly.
import sympy as sp
from itertools import combinations, product

def has_weight4_spurious(p, n):
    # find a primitive n-th root g in F_p (p==1 mod n)
    # then check if exist 4 antipodal-free exponents e0..e3 in [0,n) and signs with
    # sum s_i * g^{e_i} == 0 mod p, antipodal-free (no e_i, e_j with |e_i-e_j|=n/2).
    half=n//2
    # primitive root of unity:
    g0=sp.primitive_root(p)
    g=pow(g0,(p-1)//n,p)  # order n
    roots=[pow(g,e,p) for e in range(n)]
    # brute: this is C(n,4)*16 — fine for n<=32 small p count
    for combo in combinations(range(n),4):
        if any(abs(a-b)==half for a,b in combinations(combo,2)):continue
        for signs in product([1,-1],repeat=4):
            s=sum(sg*roots[e] for sg,e in zip(signs,combo))%p
            if s==0:
                return True
    return False

for m in [4,5]:
    n=2**m
    primes=[p for p in sp.primerange(n+1, 4000) if p%n==1][:40]
    bad=[]
    for p in primes:
        try:
            if has_weight4_spurious(p,n): bad.append(p)
        except Exception as e:
            pass
    print(f"n={n}: of {len(primes)} prize primes p==1 mod {n}, BAD (weight-4 in-field spurious): {len(bad)}")
    print(f"  bad primes: {bad[:30]}")
    print(f"  bad density: {len(bad)/len(primes):.3f}")
    # are bad primes characterized by v2(p-1)? p mod 2n? p mod (smaller cyclotomic)?
    if bad:
        def v2(k):
            c=0
            while k%2==0:k//=2;c+=1
            return c
        print(f"  bad v2(p-1): {sorted(set(v2(p-1) for p in bad))}; good v2(p-1): {sorted(set(v2(p-1) for p in primes if p not in bad))[:8]}")
