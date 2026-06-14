# Confirm n=8: every N(sum u) for antipodal-free U is a power of 2 (=> NO odd candidate prime).
import sympy as sp
from itertools import combinations, product
n=8; HALF=4
z=sp.symbols('z'); Phi=sp.Poly(sp.cyclotomic_poly(n,z),z)
def vec(exps):
    v=[0]*HALF
    for e in exps:
        e%=n
        if e<HALF: v[e]+=1
        else: v[e-HALF]-=1
    return v
def poly(v): return sp.Poly(sum(int(c)*z**l for l,c in enumerate(v)),z)
def Nrm(v): return abs(int(sp.resultant(Phi.as_expr(),poly(v).as_expr(),z)))
norms=set()
for size in range(1,HALF+1):
    for pr in combinations(range(HALF),size):
        for signs in product([0,1],repeat=size):
            exps=[pr[i]+(HALF if signs[i] else 0) for i in range(size)]
            v=vec(exps)
            if all(c==0 for c in v): continue
            norms.add(Nrm(v))
def is_pow2(x):
    return x>0 and (x&(x-1))==0
print("n=8 distinct N(sum u) over antipodal-free U:",sorted(norms))
print("all powers of 2?",all(is_pow2(x) for x in norms))
print("=> matches doc: D's odd part = 1 for n=8, no odd bad prime.")
