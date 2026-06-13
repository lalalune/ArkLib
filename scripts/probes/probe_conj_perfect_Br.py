import sympy
from collections import Counter
from itertools import product
from math import comb, factorial

def subgroup(n):
    m=(n**8-1)//n  # large prime, faithful for higher energies
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

def E_r(H,p,r):
    c=Counter()
    for t in product(H,repeat=r): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

def perm_count(n,r):
    # sum over size-r multisets of (orderings)^2; via composition/partition of r
    from sympy.utilities.iterables import partitions
    total=0
    for part in partitions(r):
        # part: dict {size:count}; multiset has parts with these block-sizes
        ms = []
        for size,cnt in part.items(): ms += [size]*cnt
        k=len(ms)  # number of distinct values used
        if k>n: continue
        orderings = factorial(r)
        for size in ms: orderings//=factorial(size)
        # number of multisets with this "shape": choose which distinct values, accounting for equal block sizes
        from collections import Counter as C2
        shape=C2(ms)
        ways=1; avail=n
        # assign distinct values to blocks; blocks of equal size are interchangeable
        import math
        num_distinct=k
        ways = math.perm(n, num_distinct)
        denom=1
        for sz,c in shape.items(): denom*=factorial(c)
        ways//=denom
        total += ways*orderings*orderings
    return total

print("A5 (perfect B_r): E_r(mu_p) vs permutation count, for r<p.  match => SURVIVES.")
print(f"{'p':>3} {'r':>2} {'r<p':>4} {'E_r(mu_p)':>11} {'perm count':>11} {'match?':>7}")
for p in (5,7,11):
    for r in (2,3,4,5):
        if r>=p: continue
        if p**r > 30_000_000: continue
        H,P=subgroup(p)
        er=E_r(H,P,r); pc=perm_count(p,r)
        print(f"{p:>3} {r:>2} {str(r<p):>4} {er:>11} {pc:>11} {str(er==pc):>7}")
print("\nAlso test r>=p (should FAIL perfect-B_r if extra relations appear):")
for p in (3,5):
    for r in (p, p+1):
        if p**r>30_000_000: continue
        H,P=subgroup(p)
        er=E_r(H,P,r); pc=perm_count(p,r)
        print(f"p={p} r={r} (r>=p): E_r={er} perm={pc} match={er==pc}  (mismatch => p-sum relation kicks in)")
