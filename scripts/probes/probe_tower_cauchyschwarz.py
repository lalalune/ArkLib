# Nail the tower recursion constant: Δ_{top} / E(μ_{n/2}) at the boundary, and the implied
# exponent log2(4+C). If C<2.35 → unconditional E≤n^{<8/3} (beats GV) via elementary tower+CS.
import sympy, math
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def E2(G,p):
    r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
print(f"{'n':>5}{'p':>9}{'E(n)':>10}{'E(n/2)':>10}{'Δtop':>9}{'Δtop/E(n/2)':>13}{'maxC->exp':>11}")
maxC=0
for m in range(4,9):
    n=2**m
    base=n*n; cand=base-(base%n)+1
    while not sympy.isprime(cand): cand+=n
    # scan a few boundary primes, take worst Δtop/E(n/2)
    worst=0; worstp=cand; cnt=0; c=cand
    while cnt<8:
        if sympy.isprime(c):
            En=E2(musub(n,c),c); Eh=E2(musub(n//2,c),c)
            dtop=En-4*Eh-6*(n//2)
            ratio=dtop/Eh if Eh else 0
            if ratio>worst: worst=ratio; worstp=c; worstEn=En; worstEh=Eh; worstd=dtop
            cnt+=1
        c+=n
    maxC=max(maxC,worst)
    print(f"{n:>5}{worstp:>9}{worstEn:>10}{worstEh:>10}{worstd:>9}{worst:>13.3f}{math.log2(4+worst):>11.3f}")
print(f"\nmax C over all = {maxC:.3f}; implied exponent log2(4+C)={math.log2(4+maxC):.3f} (GV=2.667, HBK=2.5, truth=2)")
