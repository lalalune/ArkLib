#!/usr/bin/env python3
"""
Structure of the Johnson-scale esymm fiber: are the (few) solutions exactly
subgroup-COSETS (=> sparse divisors of X^n-1 => provably poly count)?

Prior probe: Johnson-scale fiber {a-subsets T of mu_n with e_1..e_j=0,
j~a} is 0-3 (tiny). Hypothesis: the solutions are exactly UNIONS OF COSETS
of subgroups H <= mu_n (whose vanishing poly X^|H|-c is sparse, killing top
esymm). If so, the fiber count = #{such coset-unions of size a} = poly(n)
(subgroups of mu_{2^mu} are nested, count <= mu+1; cosets per subgroup <=
index). This would make the Johnson-scale list provably poly for the
monomial word -- the positive direction toward the prize.

For each fiber solution T, test: is T a union of cosets of some nontrivial
subgroup H = mu_d (d|n)? (i.e. T closed under mult by a d-th-root generator).
"""
import itertools, math

def find_prime(n, lo=200):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%dd for dd in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)], h
    raise RuntimeError
def esym_top(roots,p,j):
    a=len(roots); poly=[1]
    for r in roots:
        new=[0]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]=(new[i]+c)%p; new[i+1]=(new[i+1]-r*c)%p
        poly=new
    return tuple(((-1)**i*poly[a-i])%p for i in range(1,j+1))

def is_coset_union(T, D, h, p, n):
    """T subset mu_n (as values); is T closed under mult by h^(n/d) for some d|n, d<n?"""
    Tset=set(T); idx={D[i]:i for i in range(n)}
    for d in range(2,n):
        if n%d: continue
        gen=pow(h,n//d,p)  # generates mu_d
        # T closed under mult by gen?
        if all((t*gen)%p in Tset for t in T):
            return d  # union of mu_d-cosets
    return 0

for (n,a,j) in [(12,6,5),(24,8,7),(16,8,7),(20,10,9),(24,12,11)]:
    p=find_prime(n); D,h=smooth(p,n)
    if math.comb(n,a)>3_000_000:
        print(f"n={n} a={a}: too big"); continue
    sols=[T for T in itertools.combinations(D,a) if all(e==0 for e in esym_top(list(T),p,j))]
    structs=[is_coset_union(T,D,h,p,n) for T in sols]
    print(f"n={n} a={a} j={j}: fiber={len(sols)}; coset-subgroup d per solution: {structs} "
          f"{'(all coset-unions => sparse divisors => poly)' if sols and all(s>0 for s in structs) else ('(empty)' if not sols else '(NOT all cosets!)')}")
