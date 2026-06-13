import sympy
from collections import Counter
from itertools import product

def subgroup(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

def Z_k(H,p,k):  # # ordered k-tuples summing to 0
    c=Counter()
    for t in product(H,repeat=k): c[sum(t)%p]+=1
    return c[0]

print("Z_k(mu_n) = #{k-tuples summing to 0}.  Look for closed forms by n-structure.")
print(f"{'n':>3} {'fac':>8} {'Z2':>4} {'Z3':>6} {'Z4':>7} {'Z5':>9}")
data=[]
for n in [3,5,7,9,11,15,4,8,16,6,12,25,10,14]:
    H,p=subgroup(n)
    zs=[]
    for k in (2,3,4,5):
        if n**k>15_000_000: zs.append(None); continue
        zs.append(Z_k(H,p,k))
    fac=str(sympy.factorint(n))
    print(f"{n:>3} {fac:>8} {str(zs[0]):>4} {str(zs[1]):>6} {str(zs[2]):>7} {str(zs[3]):>9}")
    data.append((n,zs))
print("\nConjectures to check: Z2=n*[2|n]; Z3=2n*[3|n] (odd); Z4 structure; etc.")
for n,zs in data:
    z2pred = n if n%2==0 else 0
    z3pred = 2*n if (n%3==0 and n%2==1) else (0 if n%2==1 else None)
    print(f"n={n}: Z2={zs[0]} (pred {z2pred}, {'OK' if zs[0]==z2pred else 'X'});  Z3={zs[1]} (pred odd:{z3pred})")
