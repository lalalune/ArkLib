import sympy, math
from collections import Counter
from itertools import product
from math import factorial
import sympy as sp

def subgroup(n):
    m=(n**6-1)//n
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
        for s,cnt in part.items(): ms+=[s]*cnt
        k=len(ms)
        if k>n: continue
        o=factorial(r)
        for s in ms: o//=factorial(s)
        sh=C2(ms); ways=math.perm(n,k)
        for sz,c in sh.items(): ways//=factorial(c)
        total+=ways*o*o
    return total

# First-failure excess: E_q(mu_n) - perm(n,q) for odd composite n, q=minFac(n)=3.
print("D (coset-correction): excess E_3(mu_n)-perm at q=3 composites; conjecture closed form.")
print(f"{'n':>3} {'n/3':>4} {'E_3':>8} {'perm':>8} {'excess':>8}")
pts=[]
for n in (9,15,21,27,33,39):
    if n**3>5_000_000: break
    H,p=subgroup(n); e=E_r(H,p,3); pc=perm_count(n,3)
    pts.append((n, e-pc))
    print(f"{n:>3} {n//3:>4} {e:>8} {pc:>8} {e-pc:>8}")
# fit excess as polynomial in n (these all have q=3)
if len(pts)>=4:
    c=sp.symbols('c0:4')
    eqs=[sum(c[i]*N**i for i in range(4))-v for N,v in pts[:4]]
    sol=sp.solve(eqs,c)
    poly=[sol[c[i]] for i in range(4)]
    ok=all(sum(poly[i]*N**i for i in range(4))==v for N,v in pts)
    n=sp.symbols('n'); expr=sum(poly[i]*n**i for i in range(4))
    print(f"\nexcess_3(n) for q=3 composites = {sp.factor(expr)}  (verified all pts: {ok})")
