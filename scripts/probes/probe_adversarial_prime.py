# Decisive: for fixed n=2^m, is there a prime p≡1 mod n with p ≫ n^{2.5} but surplus>0
# (a parallelogram ζ^i+ζ^j=ζ^k+ζ^l mod p)? If yes → n^{2.5} NOT universal, production hard.
# Compute: for each n, scan ALL primes p≡1 mod n up to a high bound, find the LARGEST p with surplus>0.
import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def surplus(n,p):
    G=musub(n,p); char0=3*n*n-3*n
    r=Counter((a+b)%p for a in G for b in G); E=sum(v*v for v in r.values())
    return E-char0
import math
for m in [3,4,5]:
    n=2**m
    largest_bad=0; bad_ratio=0
    cnt=0; cand=n+1
    hi=int(n**4.5)
    while cand<hi and cnt<3000:
        if sympy.isprime(cand):
            s=surplus(n,cand); cnt+=1
            if s>0:
                largest_bad=cand; bad_ratio=math.log(cand)/math.log(n)
        cand+=n
    print(f"n={n}: scanned {cnt} primes p≡1 mod n up to n^{math.log(hi)/math.log(n):.1f}; "
          f"LARGEST p with surplus>0 = {largest_bad} = n^{bad_ratio:.2f}")
