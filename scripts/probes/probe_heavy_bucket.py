# Dual brick: for a FIXED codeword c and nonvanishing u₁, c gives a core (agreement ≥ a)
# to at most ⌊n/a⌋ scalars γ on the line w_γ = u₀ + γu₁.
# (Each point i agrees with w_γ for unique γ_i = (c_i − u0_i)/u1_i; agreement sets partition [n].)
from itertools import product
def codewords(Fq,n,k,dom):
    return [tuple(sum(cc[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for cc in product(range(Fq),repeat=k)]
def inv(x,Fq): return pow(x,Fq-2,Fq)
ok=True; checked=0; maxratio=0
import random; random.seed(7)
for (Fq,n,k) in [(7,6,2),(11,8,2),(11,10,3),(13,7,2)]:
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    u1=tuple(pow(dom[i],k,Fq) for i in range(n))   # x^k, nonvanishing
    assert all(x!=0 for x in u1)
    for _ in range(20):
        u0=tuple(random.randrange(Fq) for _ in range(n))
        for m in range(0,2):
            a=k+m+1
            if a>n: continue
            for c in cw:
                # γ_i for each point
                heavy={}
                for i in range(n):
                    g=( (c[i]-u0[i])*inv(u1[i],Fq) )%Fq
                    heavy[g]=heavy.get(g,0)+1
                ncore=sum(1 for g,cnt in heavy.items() if cnt>=a)
                checked+=1
                if ncore> n//a:
                    ok=False; print(f"VIOLATION F{Fq} n{n} k{k} m{m}: codeword gives {ncore} > {n//a}")
                maxratio=max(maxratio, ncore)
print(f"HEAVY-BUCKET BOUND (c gives core to ≤ ⌊n/a⌋ scalars): {ok} ({checked} checks, max observed {maxratio})")
