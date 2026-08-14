#!/usr/bin/env python3
"""
PROBE: #pinnedScalars <= #alignableSets / (min multiplicity), and does the min-mult
inversion BITE at deep bands?  If every pinned γ owns >= M aligned a-sets then
#pinned * M <= #alignable => #pinned <= #alignable / M.  We measure min-mult per band
to see whether the division is a real tightening of pinnedScalars_card_le.
Structured words on PROPER thin μ_n, prize-regime p.
"""
import itertools, random
from sympy import isprime, primitive_root

def find_p(n, beta=4):
    p=n**beta+1
    while True:
        if (p-1)%n==0 and isprime(p): return p
        p+=1
def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return sorted({pow(h,i,p) for i in range(n)})
def lowdeg(dom,k,p,c): return [sum(c[e]*pow(x,e,p) for e in range(k))%p for x in dom]
def residual_val(u,tup,dom,k,p):
    xs=[dom[i] for i in tup]; ys=[u[i] for i in tup]
    M=[[pow(xs[j],e,p) for e in range(k)]+[ys[j]] for j in range(k)]; m=k
    for col in range(m):
        piv=None
        for r in range(col,m):
            if M[r][col]%p!=0: piv=r;break
        if piv is None: return 1
        M[col],M[piv]=M[piv],M[col]; inv=pow(M[col][col],p-2,p)
        M[col]=[(v*inv)%p for v in M[col]]
        for r in range(m):
            if r!=col and M[r][col]%p!=0:
                f=M[r][col]; M[r]=[(M[r][i]-f*M[col][i])%p for i in range(m+1)]
    coeffs=[M[i][m]%p for i in range(m)]
    return (sum(coeffs[e]*pow(xs[k],e,p) for e in range(k))-ys[k])%p

def analyze(n,k,a,beta,seed,s):
    p=find_p(n,beta); dom=mu_n(p,n); random.seed(seed)
    s=min(s,n); 
    T=sorted(random.sample(range(n),s))
    cA=[random.randrange(p) for _ in range(k)]; cB=[random.randrange(p) for _ in range(k)]
    fA=lowdeg(dom,k,p,cA); fB=lowdeg(dom,k,p,cB)
    u0=[random.randrange(p) for _ in range(n)]; u1=[random.randrange(p) for _ in range(n)]
    for i in T: u0[i]=fA[i]; u1[i]=fB[i]
    mult={}  # gamma -> count aligned a-sets
    nal=0
    for S in itertools.combinations(range(n),a):
        ts=list(itertools.combinations(S,k+1)); cand=None; nd=False
        for t in ts:
            r0=residual_val(u0,t,dom,k,p); r1=residual_val(u1,t,dom,k,p)
            if not(r0==0 and r1==0):
                nd=True
                cand=(-r0*pow(r1,p-2,p))%p if r1%p!=0 else None
                break
        if not nd or cand is None: continue
        if all((residual_val(u0,t,dom,k,p)+cand*residual_val(u1,t,dom,k,p))%p==0 for t in ts):
            nal+=1; mult[cand]=mult.get(cand,0)+1
    if not mult: return p,0,0,0,0
    npn=len(mult); minm=min(mult.values()); maxm=max(mult.values())
    return p,npn,nal,minm,maxm

print("n  k a  s  p      #pinned #alignable minMult maxMult  pinned<=incid/minMult?")
for (n,k,a,beta,s) in [(8,2,4,4,5),(8,2,4,4,6),(8,2,5,4,6),(16,2,5,4,8),(16,2,6,4,10),(16,2,6,4,12)]:
    for seed in [1,2]:
        p,npn,nal,minm,maxm=analyze(n,k,a,beta,seed,s)
        if npn==0:
            print(f"{n:2} {k} {a} {s:2} {p:6}  (no pinned)"); continue
        bound=nal//minm if minm>0 else nal
        ok="YES" if npn<=bound else "NO!!"
        tighter="TIGHTER" if bound<nal else "same"
        print(f"{n:2} {k} {a} {s:2} {p:6}  {npn:4}    {nal:5}     {minm:4}   {maxm:4}    {ok} (incid/minMult={bound}, {tighter})")
