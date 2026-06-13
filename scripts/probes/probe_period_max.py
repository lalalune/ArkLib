# DECISIVE: is max_{t≠0}|η_t|² ≤ C·n for the 2-power subgroup (⟹ E≤Cn² self-contained)?
# η_t = Σ_{y∈μ_n} e_p(ty). Compute max over t≠0, ratio to n, across n and p-regimes.
import sympy, cmath
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def maxperiod_sq(n,p):
    G=musub(n,p); w=2*cmath.pi/p; mx=0
    for t in range(1,p):
        s=sum(cmath.exp(1j*w*((t*y)%p)) for y in G)
        a=abs(s)**2
        if a>mx: mx=a
    return mx
import math
print(f"{'n':>4}{'p':>8}{'p/n^k':>7}{'max|η|²(t≠0)':>14}{'/n':>7}{'√p':>8}{'√n':>7}")
for (m,kk) in [(3,2.0),(3,3.0),(4,2.0),(4,2.5),(4,3.0),(5,2.0),(5,2.5),(5,3.0),(6,2.0),(6,2.5)]:
    n=2**m; target=int(n**kk); p=None
    for cand in range(target-target%n+1, target*3, n):
        if sympy.isprime(cand): p=cand;break
    if not p: continue
    mx=maxperiod_sq(n,p)
    print(f"{n:>4}{p:>8}{math.log(p)/math.log(n):>7.2f}{mx:>14.1f}{mx/n:>7.2f}{math.sqrt(p):>8.1f}{math.sqrt(n):>7.2f}")
