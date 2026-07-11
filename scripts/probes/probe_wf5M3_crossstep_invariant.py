import numpy as np
from sympy import primitive_root
def setup(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    G=[];x=1
    for _ in range(n):G.append(x);x=(x*h)%p
    return sorted(G)
def df(k):
    pr=1
    while k>0:pr*=k;k-=2
    return pr
# CORRECT per-step lemma to propagate E_r <= (2r-1)!! n^r:
#   E_{r+1} = n E_r + cross_r <= (2r+1)!! n^{r+1}
#   <=> cross_r <= (2r+1)!! n^{r+1} - n E_r
# If E_r is AT ceiling: cross_r <= [(2r+1)!!-(2r-1)!!] n^{r+1} = 2r*(2r-1)!! n^{r+1}.
# The RIGHT sufficient lemma (slack-aware): cross_r <= 2r * n * (2r-1)!! n^r  [= 2rn * CEILING, not 2rn*E_r]
# i.e.  cross_r <= 2r*n^{r+1}*(2r-1)!!   --- an ABSOLUTE bound, not relative to E_r.
print("ABSOLUTE per-step lemma: cross_r <= 2r * (2r-1)!! * n^{r+1} ?  (propagates ceiling if E_r<=ceil_r)")
print(f"{'p':>6}{'n':>3}{'r':>3}{'cross_r/[2r(2r-1)!!n^(r+1)]':>28}{'HOLDS?':>7}")
for (p,n,rmax) in [(7681,16,5),(3457,8,5),(61441,32,4),(12289,16,5)]:
    if (p-1)%n:continue
    G=setup(p,n)
    f=np.zeros(p,dtype=object)
    for s in G:f[s]=1
    for r in range(1,rmax+1):
        if r>1:
            fn=np.zeros(p,dtype=object)
            for s in G:fn+=np.roll(f,s)
            f=fn
        e=int((f.astype(object)**2).sum())
        tot=0
        for s in G:
            for t in G:tot+=int((f*np.roll(f,-((s-t)%p))).sum())
        cr=tot-n*e
        bound=2*r*df(2*r-1)*n**(r+1)
        rr=cr/bound
        print(f"{p:>6}{n:>3}{r:>3}{rr:>28.4f}{'Y' if cr<=bound else 'N':>7}")
