from sympy import primerange, primitive_root
from collections import Counter

def mu_n(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    return [pow(h,k,p) for k in range(n)]
def rEnergy(G,p,r):
    f=Counter({0:1})
    for _ in range(r):
        f2=Counter()
        for d,c in f.items():
            for s in G: f2[(d+s)%p]+=c
        f=f2
    return sum(c*c for c in f.values())

# Need E_3 <= 15n^3 - 3n^2 to close r=2 rung from sharp E_2.
# Measure true E_3 vs 15n^3-3n^2 (sharpened ceiling) and vs 12n^3+n*E_2 (the exact requirement).
print("n   E3        15n^3-3n^2  E3<=that? | 12n^3+nE2(req)  E3<=req?  | E3/n^3")
for a in range(2,7):
    n=2**a
    target=n**4*2
    p=None
    for c in primerange(target,target*8):
        if (c-1)%n==0: p=c; break
    G=mu_n(p,n)
    E2=rEnergy(G,p,2); E3=rEnergy(G,p,3)
    sharp=15*n**3-3*n**2
    req=12*n**3+n*E2
    print(f"{n:<3} {E3:<9} {sharp:<11} {str(E3<=sharp):<8} | {req:<13} {str(E3<=req):<8} | {E3/n**3:.4f}")
