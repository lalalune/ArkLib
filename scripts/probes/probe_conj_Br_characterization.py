import sympy
from collections import Counter
from itertools import product
import math
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
        orderings=factorial(r)
        for size in ms: orderings//=factorial(size)
        shape=C2(ms)
        ways=math.perm(n,k)
        for sz,c in shape.items(): ways//=factorial(c)
        total+=ways*orderings*orderings
    return total

def minfac(n):
    for q in range(2,n+1):
        if n%q==0: return q
    return n

print("A6: mu_n perfect B_r  <=>  even:r=1 / odd-prime:all r / odd-comp: r<minFac(n)")
print(f"{'n':>3} {'minFac':>6} {'r':>2} {'predict B_r?':>12} {'E_r==perm?':>11} {'AGREE?':>7}")
for n in [9,15,25,21,27]:
    q=minfac(n)
    for r in (2,3,4,5):
        if n**r>25_000_000: continue
        H,p=subgroup(n); er=E_r(H,p,r); pc=perm_count(n,r)
        predict = (r < q) or sympy.isprime(n)
        actual = (er==pc)
        print(f"{n:>3} {q:>6} {r:>2} {str(predict):>12} {str(actual):>11} {'OK' if predict==actual else 'MISMATCH!':>7}")
