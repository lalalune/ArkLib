from sympy import primerange, primitive_root
from collections import Counter
def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,k,p) for k in range(n)]
def rEnergy(G,p,r):
    f=Counter({0:1})
    for _ in range(r):
        f2=Counter()
        for d,c in f.items():
            for s in G: f2[(d+s)%p]+=c
        f=f2
    return sum(c*c for c in f.values())
# E_2 = 3n^2-3n exact. Is E_3 a clean polynomial in n on mu_n (char-0-faithful regime)?
# Conjecture forms: 15n^3 + a*n^2 + b*n. Fit from data.
print("n   E3        15n^3     E3-15n^3   /n^2    /n")
data=[]
for a in range(2,8):
    n=2**a
    target=n**5  # very large prime to stay char-0 faithful for r=3
    p=None
    for c in primerange(target,target*4):
        if (c-1)%n==0: p=c; break
    if p is None: continue
    E3=rEnergy(G:=mu_n(p,n),p,3)
    diff=E3-15*n**3
    data.append((n,E3,diff))
    print(f"{n:<3} {E3:<9} {15*n**3:<9} {diff:<10} {diff/n**2:<7.3f} {diff/n:.3f}")
# try to fit diff = a*n^2 + b*n
if len(data)>=3:
    import numpy as np
    ns=np.array([d[0] for d in data],dtype=float)
    diffs=np.array([d[2] for d in data],dtype=float)
    A=np.vstack([ns**2, ns]).T
    coef,res,_,_=np.linalg.lstsq(A,diffs,rcond=None)
    print(f"\nfit diff ≈ {coef[0]:.4f}*n^2 + {coef[1]:.4f}*n  (residual {res})")
