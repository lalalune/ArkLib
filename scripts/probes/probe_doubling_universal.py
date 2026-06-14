# Is E(μ_{2n}) = 4E(μ_n)+6n UNIVERSAL (all p≡1 mod 2n) or only above threshold?
import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(G,p):
    r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
import math
print(f"{'n':>4}{'p':>8}{'p/n^k':>7}{'E(n)':>8}{'E(2n)':>8}{'4E+6n':>8}{'recur?':>7}{'E(2n)-4E(n)':>12}")
for m in range(3,7):
    n=2**m; n2=2*n
    for kk in [1.5,1.8,2.0,2.5,3.0]:
        target=int(n2**kk); p=None
        for cand in range(max(target-target%n2+1,2*n2+1), target*4, n2):
            if sympy.isprime(cand): p=cand;break
        if not p: continue
        Gn=musub(n,p); G2n=musub(n2,p)
        en,e2n=E2(Gn,p),E2(G2n,p)
        print(f"{n:>4}{p:>8}{math.log(p)/math.log(n):>7.2f}{en:>8}{e2n:>8}{4*en+6*n:>8}{str(e2n==4*en+6*n):>7}{e2n-4*en:>12}")
