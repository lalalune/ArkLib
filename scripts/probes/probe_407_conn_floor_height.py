# Verify: floor bad primes (spurious config exists) divide gcd(N(sum u), N(sum u^3)), height <= (2r)^{phi(s)}
import sympy as sp
from itertools import combinations
s=16; HALF=8; r=3   # config size 2r=6 in mu_16
z=sp.symbols('z'); Phi=sp.Poly(sp.cyclotomic_poly(s,z),z)
def vec(exps):
    v=[0]*HALF
    for e in exps:
        e%=s
        if e<HALF: v[e]+=1
        else: v[e-HALF]-=1
    return v
def poly(v): return sp.Poly(sum(int(c)*z**l for l,c in enumerate(v)),z)
def N(v): return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))
# the floor-bad prime 17 (n=16): show it divides gcd(N(sum u),N(sum u^3)) for the actual spurious config
maxfac=0
for pr in combinations(range(HALF),2*r):
    for signs in range(2**(2*r)):
        exps=[pr[i]+(HALF if (signs>>i)&1 else 0) for i in range(2*r)]
        a=vec(exps); b=vec([3*e for e in exps])
        if all(c==0 for c in a) or all(c==0 for c in b): continue
        g=sp.gcd(N(a),N(b))
        for p,_ in sp.factorint(g).items():
            if p%2==1 and p%s==1: maxfac=max(maxfac,p)
print(f"mu_16 floor: max odd prime===1 mod s dividing gcd(N(sumU),N(sumU3)) over all configs = {maxfac}")
print(f"height bound (2r)^(phi(s)) = {(2*r)**HALF} (log2={HALF*sp.log(2*r,2).evalf():.1f}); 4^s window bottom=2^{2*s}")
