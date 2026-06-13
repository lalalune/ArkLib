# Pin the worst-case E/n² scaling: is it log n, log²n, or n^ε? Focus near p~n² (hardest).
import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(n,p):
    G=musub(n,p); r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
import math
print(f"{'n':>5}{'m':>4}{'maxE/n²':>9}{'/(log n)':>10}{'/(log²n)':>10}{'worst p/n²':>11}")
for m in range(3,8):
    n=2**m; maxr=0; maxp=0; cnt=0
    base=int(n**1.9); cand=base-(base%n)+1; hi=int(n**2.4)
    while cand<hi and cnt<6000:
        if sympy.isprime(cand):
            E=E2(n,cand); cnt+=1
            if E/(n*n)>maxr: maxr=E/(n*n); maxp=cand
        cand+=n
    ln=math.log(n)
    print(f"{n:>5}{m:>4}{maxr:>9.2f}{maxr/ln:>10.3f}{maxr/(ln*ln):>10.3f}{maxp/(n*n):>11.2f}")
