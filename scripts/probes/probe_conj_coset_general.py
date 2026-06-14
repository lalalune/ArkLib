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
        for s,cnt in part.items(): ms+=[s]*cnt
        k=len(ms)
        if k>n: continue
        o=factorial(r)
        for s in ms: o//=factorial(s)
        sh=C2(ms); ways=math.perm(n,k)
        for sz,c in sh.items(): ways//=factorial(c)
        total+=ways*o*o
    return total

print("D general: E_q(mu_n)-perm = (q!)^2 * (n/q)(n/q-1) for q=minFac(n).")
for n,q in [(9,3),(15,3),(25,5),(21,3),(35,5),(49,7)]:
    if n**q > 12_000_000: 
        print(f"n={n} q={q}: too big to brute-force, skip"); continue
    H,p=subgroup(n); e=E_r(H,p,q); pc=perm_count(n,q)
    pred=factorial(q)**2 * (n//q)*(n//q-1)
    print(f"n={n} q={q}: excess={e-pc:>8}  predicted (q!)^2*(n/q)(n/q-1)={pred:>8}  match={e-pc==pred}")
