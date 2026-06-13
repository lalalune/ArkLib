# The line-list reduction: #{γ : some codeword agrees with w_γ on ≥a pts}
#   ≤ #{appearing codewords} · ⌊n/a⌋.
# Verify the inequality (and see how tight) across params.
from itertools import product
def codewords(Fq,n,k,dom):
    return [tuple(sum(cc[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for cc in product(range(Fq),repeat=k)]
def inv(x,Fq): return pow(x,Fq-2,Fq)
import random; random.seed(11); ok=True
for (Fq,n,k) in [(7,6,2),(11,8,2),(11,10,3),(13,7,2)]:
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    u1=tuple(pow(dom[i],k,Fq) for i in range(n))
    for _ in range(15):
        u0=tuple(random.randrange(Fq) for _ in range(n))
        for m in range(0,2):
            a=k+m+1
            if a>n: continue
            badG=set(); appC=set()
            for ci,c in enumerate(cw):
                gives=False
                for g in range(Fq):
                    ag=sum(1 for i in range(n) if c[i]==(u0[i]+g*u1[i])%Fq)
                    if ag>=a:
                        badG.add(g); gives=True
                if gives: appC.add(ci)
                # also enforce c is a real codeword (it is)
            lhs=len(badG); rhs=len(appC)*(n//a)
            if lhs>rhs: ok=False; print(f"VIOLATION F{Fq} n{n} k{k} m{m}: {lhs}>{rhs}")
print("LINE-LIST REDUCTION (#badγ ≤ #appearing·⌊n/a⌋):", ok)
