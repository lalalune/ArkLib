# NEW ANGLE: the Gauss-period magnitude distribution of μ_n (n=2^m) in F_p.
# η_t = Σ_{y∈μ_n} ω^{ty}, ω=e_p. E(μ_n) = (1/p)Σ_t |η_t|². Wait: E = (1/p)Σ_t |Ŝ(t)|⁴
# where Ŝ(t)=Σ_{y∈μ_n} ω^{ty}. If |Ŝ(t)|² takes few values, E is exact & maybe ≤Cn².
import sympy, cmath
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def periods_absq(n,p):
    G=musub(n,p); w=2*cmath.pi/p
    vals=[]
    for t in range(p):
        s=sum(cmath.exp(1j*w*((t*y)%p)) for y in G)
        vals.append(round(abs(s)**2,4))
    return vals
for (n,p) in [(8,73),(8,257),(16,97),(16,193),(16,257),(16,577)]:
    v=periods_absq(n,p)
    E=sum(x*x for x in v)/p
    c=Counter(round(x,1) for x in v)
    top=sorted(c.items(),key=lambda kv:-kv[1])[:6]
    import math
    print(f"n={n} p={p}: E={E:.0f} (3n²={3*n*n}); |η|² distribution (val:count) top: {top}; max|η|²={max(v):.1f} (n²={n*n}, p={p})")
