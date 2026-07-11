import sympy
def mu_n(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, k, p) for k in range(n)})
def rEnergy(G, p, r):
    from collections import Counter
    dist = Counter({0:1})
    for _ in range(r):
        nd = Counter()
        for s,c in dist.items():
            for x in G:
                nd[(s+x)%p]+=c
        dist=nd
    return sum(c*c for c in dist.values())
# Fit E4 to a*n^4+b*n^3+c*n^2+d*n using exact integer values, to identify the closed form.
data=[]
for n in [4,8,16,32,64]:
    lo = n**4
    cand = lo - (lo % n) + 1
    p=None
    while True:
        if cand % n == 1 and sympy.isprime(cand) and cand>n**4:
            p=cand; break
        cand += n
    G = mu_n(p,n)
    assert len(G)==n
    E3=rEnergy(G,p,3); E4=rEnergy(G,p,4)
    data.append((n,E3,E4))
    print("n=%d E4=%d  E4/E3=%.4f (7n=%d)  E4/(105n^4)=%.5f" % (n,E4,E4/E3,7*n,E4/(105*n**4)))
# solve for polynomial coeffs a n^4 + b n^3 + c n^2 + d n + e using 5 points
import sympy as sp
a,b,c,d,e=sp.symbols('a b c d e')
eqs=[a*n**4+b*n**3+c*n**2+d*n+e - E4 for (n,_,E4) in data]
sol=sp.solve(eqs,[a,b,c,d,e],dict=True)
print("E4 closed form coeffs (n^4,n^3,n^2,n,1):", sol)
