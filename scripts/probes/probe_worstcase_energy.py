import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(n,p):
    G=musub(n,p); r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
import math
for m in [3,4,5]:
    n=2**m
    maxE=0; maxp=0; cnt=0
    base=n*n
    cand=base - (base % n) + 1   # first ≡1 mod n above n²
    hi=int(n**4)
    while cand<hi and cnt<4000:
        if sympy.isprime(cand):
            E=E2(n,cand); cnt+=1
            if E>maxE: maxE=E; maxp=cand
        cand+=n
    print(f"n={n}: {cnt} primes in [n²,n⁴]: MAX E={maxE} at p={maxp}=n^{math.log(maxp)/math.log(n):.2f}; "
          f"maxE/n²={maxE/(n*n):.2f}; n^(2/3)={n**(2/3):.1f}; char0 E/n²=3")
