import sympy, math
from collections import Counter
from itertools import product
from math import factorial
import sympy as sp

def subgroup(n):
    m=(n**8-1)//n
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
    from sympy.utilities.iterables import partitions
    from collections import Counter as C2
    total=0
    for part in partitions(r):
        ms=[]
        for size,cnt in part.items(): ms+=[size]*cnt
        k=len(ms)
        if k>n: continue
        o=factorial(r)
        for s in ms: o//=factorial(s)
        sh=C2(ms); ways=math.perm(n,k)
        for sz,c in sh.items(): ways//=factorial(c)
        total+=ways*o*o
    return total

# antipodal excess closed forms, with n=64 added for r=3,4 fits
for r in (2,3,4):
    pts=[]
    for k in (2,3,4,5,6):
        n=1<<k
        if n**r>1.2e9: break
        H,p=subgroup(n); pts.append((n, E_r(H,p,r)-perm_count(n,r)))
    if len(pts)<r+1: print(f"r={r}: pts={pts}"); continue
    c=sp.symbols(f'c0:{r+1}')
    eqs=[sum(c[i]*N**i for i in range(r+1))-v for N,v in pts]
    sol=sp.solve(eqs[:r+1],c)
    poly=[sol[c[i]] for i in range(r+1)]
    # verify on remaining points
    ok=all(sum(poly[i]*N**i for i in range(r+1))==v for N,v in pts)
    print(f"r={r}: antipodal excess = {poly} (verified all {len(pts)} pts: {ok})  factored:")
    n=sp.symbols('n'); expr=sum(poly[i]*n**i for i in range(r+1))
    print(f"        = {sp.factor(expr)}")
