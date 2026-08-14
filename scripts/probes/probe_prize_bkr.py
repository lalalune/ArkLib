#!/usr/bin/env python3
"""
THE lead: do dyadic smooth domains mu_{2^mu} support BKR-style sub-Johnson
list explosions? (the multiplicative analog of Ben-Sasson-Kopparty-
Radhakrishnan FOCS'06 subspace-polynomial list lower bounds).

BKR06: RS on a SUBSPACE eval set has >poly list just beyond Johnson, built
from subspace (linearized) polynomials. Multiplicative analog: mu_{2^mu}
has subgroups H_j = mu_{2^j} (all j<=mu) and cosets. A word w that equals a
deg<k codeword on each coset of a subgroup H (|H| points each) could be
agreed-with by MANY codewords if the coset-agreement polynomials are
low-degree. If the list explodes for dyadic n, ExplainableCoreSupply FAILS
=> delta* pinned BELOW capacity for smooth dyadic RS (the prize regime!).

Test: n=2^mu, build w by stitching different deg<k codewords on different
cosets of a subgroup H (size h); count deg<k codewords agreeing with w on
>= a points, compare to Johnson ~sqrt(kn). Look for super-Johnson list.
"""
import itertools, math
from collections import Counter

def smooth_domain(p, n):
    assert (p-1) % n == 0
    for cand in range(2, p):
        h = pow(cand, (p-1)//n, p)
        if all(pow(h, j, p) != 1 for j in range(1, n)) and pow(h, n, p) == 1:
            return [pow(h, j, p) for j in range(n)], h
    raise RuntimeError

def all_cw(D, p, k):
    n=len(D)
    for c in itertools.product(range(p), repeat=k):
        yield c, tuple(sum(c[t]*pow(x,t,p) for t in range(k))%p for x in D)

def listsize(D,p,k,w,a):
    return sum(1 for _,cw in all_cw(D,p,k) if sum(1 for i in range(len(D)) if cw[i]==w[i])>=a)

# dyadic cases: n=2^mu, q^k enumerable
CASES=[(17,16,2),(17,8,3),(41,8,3),(97,16,2)]
for (p,n,k) in CASES:
    if (p-1)%n: print(f"skip ({p},{n},{k})"); continue
    D,g=smooth_domain(p,n)
    johnson=math.isqrt(k*n)
    # subgroup H = mu_{n/2} indices (even powers of g): D[0,2,4,...]
    # build w: codeword A on even-index coset, codeword B on odd-index coset
    import random; rng=random.Random(3)
    best=(0,0,None)
    for trial in range(60):
        cA=[rng.randrange(p) for _ in range(k)]; cB=[rng.randrange(p) for _ in range(k)]
        w=[0]*n
        for i in range(n):
            c = cA if i%2==0 else cB
            w[i]=sum(c[t]*pow(D[i],t,p) for t in range(k))%p
        w=tuple(w)
        # list at deep-band agreement a = k+1 .. johnson
        for a in range(k+1, johnson+1):
            ls=listsize(D,p,k,w,a)
            if ls>best[0]: best=(ls,a,"coset-stitch")
    # compare: random w baseline at a=k+1
    rr=tuple(rng.randrange(p) for _ in range(n))
    base=listsize(D,p,k,rr,k+1)
    print(f"p={p} n={n}=2^{n.bit_length()-1} k={k} rho={k/n:.3f} Johnson~{johnson}: "
          f"coset-stitch max list={best[0]} at a={best[1]} (vs random-w list@{k+1}={base}); "
          f"super-Johnson? list at a>johnson would need a>{johnson}")
