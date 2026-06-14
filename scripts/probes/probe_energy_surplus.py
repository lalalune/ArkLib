import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(G,p):
    r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
import math
print(f"{'n':>4}{'p':>9}{'p/n^k':>8}{'E':>9}{'char0':>9}{'surplus':>9}{'surp/n':>8}{'surp/n²·p/n²':>14}")
for m in range(4,8):
    n=2**m; char0=3*n*n-3*n
    for kk in [1.8,2.0,2.3,2.6,3.0]:
        target=int(n**kk)
        p=None
        for cand in range(target-target%n+1, target*3, n):
            if cand>n and sympy.isprime(cand): p=cand;break
        if not p: continue
        G=musub(n,p); E=E2(G,p); surp=E-char0
        print(f"{n:>4}{p:>9}{math.log(p)/math.log(n):>8.2f}{E:>9}{char0:>9}{surp:>9}{surp/n:>8.2f}{surp*p/(n**4):>14.3f}")
