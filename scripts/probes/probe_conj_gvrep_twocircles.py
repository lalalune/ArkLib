import sympy
from collections import Counter

def subgroup(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

def maxfiber_and_M2(H,p,n):
    vals=[pow((1+x)%p,n,p) for x in H]
    c=Counter(vals)
    return max(c.values()), sum(v*v for v in c.values())

print("G: maxfiber (=max GV rep count r(c)) of zeta->(1+zeta)^n over C. Refute if any > 2.")
worst=0; allok=True
for n in range(3,60):
    H,p=subgroup(n)
    mf,m2=maxfiber_and_M2(H,p,n)
    pred = 2*n-1 if n%2 else 2*n-2
    if mf>2 or m2!=pred:
        allok=False
        print(f"  n={n}: maxfiber={mf} (>2!) OR M2={m2}!={pred}  <-- DEVIATION")
    worst=max(worst,mf)
print(f"n=3..59: max over all maxfibers = {worst}; M2=2n-1-[2|n] holds for all = {allok}")
print("=> if worst==2 and allok: G SURVIVES (r(c)<=2 over C, M2 closed form). Refuted if worst>2.")
