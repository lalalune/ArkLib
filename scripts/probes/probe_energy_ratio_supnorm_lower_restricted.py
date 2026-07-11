import cmath, math
from collections import Counter
def setup(p,n):
    def is_primroot(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_primroot(g): g+=1
    m=(p-1)//n
    mu=sorted({pow(g,(m*k)%(p-1),p) for k in range(n)})
    assert len(mu)==n
    w=[cmath.exp(2j*cmath.pi*t/p) for t in range(p)]
    norms=[]
    for b in range(p):
        s=sum(w[(b*x)%p] for x in mu)
        norms.append(abs(s)**2)
    return mu,norms
def Er(mu,p,r):
    N=Counter({0:1})
    for _ in range(r):
        M=Counter()
        for t,c in N.items():
            for a in mu: M[(t+a)%p]+=c
        N=M
    return sum(c*c for c in N.values())
def restricted(mu,p,r):
    n=len(mu)
    return p*Er(mu,p,r) - n**(2*r)   # = sum_{b!=0} |eta_b|^{2r}
print("restricted (b!=0) ratio A_{r+1}/A_r  vs  max_{b!=0}||eta||^2 (non-principal max)")
allok=True
for p,n in [(257,16),(769,16),(12289,16),(65537,16),(193,32)]:
    if (p-1)%n: continue
    mu,norms=setup(p,n)
    nonprinc=max(norms[b] for b in range(1,p))
    A=[restricted(mu,p,r) for r in range(0,4)]
    ratios=[A[r+1]/A[r] for r in range(0,3) if A[r]>0]
    ok=all(rt<=nonprinc+1e-6 for rt in ratios)
    allok=allok and ok
    beta=math.log(p)/math.log(n)
    print(f"p={p:6} n={n:3} beta={beta:.2f}  M_nonprinc^2={nonprinc:9.2f}  "
          f"ratios={['%.2f'%x for x in ratios]}  ok={ok}")
print("ALL OK:", allok, "=> restricted ratio A_{r+1}/A_r <= M(n)^2 (non-principal), tightens upward")
