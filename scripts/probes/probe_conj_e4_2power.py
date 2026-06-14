import sympy
from collections import Counter
from itertools import product
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

ns=[4,8,16,32,64]; vals=[]
for n in ns:
    H,p=subgroup(n); vals.append(E_r(H,p,4))
    print(f"n={n}: E_4={vals[-1]}")
x=sp.symbols('x'); c=sp.symbols('c0:5')
eqs=[sum(c[i]*n**i for i in range(5))-v for n,v in zip(ns,vals)]
sol=sp.solve(eqs,c)
poly=[sol[c[i]] for i in range(5)]
print(f"\nE_4(mu_2^k) = {poly[4]}*n^4 + {poly[3]}*n^3 + {poly[2]}*n^2 + {poly[1]}*n + {poly[0]}")
print(f"leading {poly[4]} vs (2*4-1)!!=105  match={poly[4]==105}")
