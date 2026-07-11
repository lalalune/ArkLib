import sympy
from collections import Counter
from itertools import product

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

def dfac(r):
    v=1
    for j in range(1,2*r,2): v*=j
    return v

def fit_poly(ns, vals, deg):
    # least-deg integer-ish polynomial through points (exact via solve)
    import sympy as sp
    x=sp.symbols('x'); coeffs=sp.symbols(f'c0:{deg+1}')
    eqs=[sum(coeffs[i]*n**i for i in range(deg+1))-v for n,v in zip(ns,vals)]
    sol=sp.solve(eqs[:deg+1], coeffs)
    return [sol[coeffs[i]] for i in range(deg+1)]

print("B3: E_r(mu_2^k) leading term = (2r-1)!! n^r ?  Fit exact polynomial, check leading coeff.")
for r in (2,3,4):
    ns=[]; vals=[]
    for k in (2,3,4,5):
        n=1<<k
        if n**r>20_000_000: break
        H,p=subgroup(n); ns.append(n); vals.append(E_r(H,p,r))
    if len(ns)<r+1:
        print(f"r={r}: only {len(ns)} points (need {r+1} for degree-r fit); vals={vals}"); continue
    co=fit_poly(ns, vals, r)
    lead=co[r]
    print(f"r={r}: E_r(mu_2^k) = {co[r]}*n^{r} + ... (leading); (2r-1)!!={dfac(r)}; match={lead==dfac(r)}")
    print(f"        poly coeffs (c0..c{r}) = {co}   data n={ns} vals={vals}")
