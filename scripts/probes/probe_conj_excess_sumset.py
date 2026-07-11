import sympy, math
from collections import Counter
from itertools import product
from math import factorial

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
        for size,cnt in part.items(): ms+=[size]*cnt
        k=len(ms)
        if k>n: continue
        o=factorial(r)
        for s in ms: o//=factorial(s)
        sh=C2(ms); ways=math.perm(n,k)
        for sz,c in sh.items(): ways//=factorial(c)
        total+=ways*o*o
    return total

def kset_sum(H,p,k):  # |k-fold sumset|
    s={0}
    for _ in range(k):
        s={(a+b)%p for a in s for b in H}
    return len(s)

print("=== C1: antipodal excess E_r(mu_2^k) - perm(n,r) closed form ===")
print(f"{'r':>2} {'n':>4} {'excess':>10} {'(2r-1)!!-r!':>12}")
def dfac(r):
    v=1
    for j in range(1,2*r,2): v*=j
    return v
ex_data={}
for r in (2,3,4):
    for k in (3,4,5):
        n=1<<k
        if n**r>20_000_000: continue
        H,p=subgroup(n); ex=E_r(H,p,r)-perm_count(n,r)
        ex_data.setdefault(r,[]).append((n,ex))
        print(f"{r:>2} {n:>4} {ex:>10} {dfac(r)-factorial(r):>12} (lead coeff)")
# fit excess polynomials
import sympy as sp
for r,pts in ex_data.items():
    if len(pts)<r+1: 
        print(f"  r={r}: need more points"); continue
    c=sp.symbols(f'c0:{r+1}')
    eqs=[sum(c[i]*n**i for i in range(r+1))-v for n,v in pts]
    sol=sp.solve(eqs[:r+1],c)
    print(f"  r={r} excess poly: {[sol[c[i]] for i in range(r+1)]}")

print("\n=== C4: triple-sumset |3*mu_n| for odd n (conjecture: full saturation?) ===")
for n in (5,7,11,13):
    H,p=subgroup(n)
    print(f"n={n}: |H|={n}, |H+H|={kset_sum(H,p,2)}, |3H|={kset_sum(H,p,3)}, |4H|={kset_sum(H,p,4)}")
