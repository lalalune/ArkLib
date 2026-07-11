import sympy, cmath, math
from collections import Counter
from itertools import product

def subgroup(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

# H: sum_{zeta in mu_n} |1+zeta|^{2k} = n*C(2k,k) for k<n (over C). Compute with complex roots.
print("H: sum_zeta |1+zeta|^{2k} = n*C(2k,k) for k<n (over C, complex roots of unity).")
for n in (5,7,11):
    roots=[cmath.exp(2j*math.pi*t/n) for t in range(n)]
    for k in (1,2,3,4):
        if k>=n: continue
        s=sum(abs(1+z)**(2*k) for z in roots)
        pred=n*math.comb(2*k,k)
        print(f"  n={n} k={k}: sum={s:.4f}  n*C(2k,k)={pred}  match={abs(s-pred)<1e-6}")

# E5: for even n, Z_{2r}(mu_n) = E_r(mu_n) (via negation -mu_n=mu_n).
def subg(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)],p
def Z(H,p,k):
    c=Counter()
    for t in product(H,repeat=k): c[sum(t)%p]+=1
    return c[0]
def E(H,p,r):
    c=Counter()
    for t in product(H,repeat=r): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())
print("\nE5: even n, Z_{2r}(mu_n) == E_r(mu_n) ?")
for n in (4,8,6,12,16):
    H,p=subg(n)
    for r in (2,3):
        if n**(2*r)>20_000_000: continue
        z=Z(H,p,2*r); e=E(H,p,r)
        print(f"  n={n} r={r}: Z_{2*r}={z}  E_{r}={e}  match={z==e}")
