# The DEPLOYED boundary n≈√p (p≈n²). Is E/(n²log n) bounded there (tractable) or growing (hard)?
# Test the smallest few primes p≡1 mod n with p≥n² (i.e. n≤√p, just inside), worst case.
import sympy
from collections import Counter
import math
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(n,p):
    G=musub(n,p); r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
print(f"{'n':>5}{'p(≈n²)':>9}{'E':>9}{'E/n²':>7}{'E/(n²ln n)':>11}{'maxrep':>7}")
for m in range(3,9):
    n=2**m
    # take the few smallest primes p≡1 mod n with p≥n², record worst E
    base=n*n; cand=base-(base%n)+1; found=[]
    while len(found)<5:
        if sympy.isprime(cand): found.append(cand)
        cand+=n
    worst=max(found, key=lambda p:E2(n,p))
    E=E2(n,worst)
    G=musub(n,worst)
    rr=Counter((a-b)%worst for a in G for b in G if a!=b)
    mr=max((v for t,v in rr.items() if t!=0),default=0)
    print(f"{n:>5}{worst:>9}{E:>9}{E/(n*n):>7.2f}{E/(n*n*math.log(n)):>11.3f}{mr:>7}")
