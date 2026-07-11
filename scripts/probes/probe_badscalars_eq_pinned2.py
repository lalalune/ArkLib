#!/usr/bin/env python3
"""
PROBE v2: badScalars == pinnedScalars on STRUCTURED words (non-vacuous bad set).

Use u0, u1 built so the combined line u0+gamma*u1 hits low-degree codewords for
several gammas (forcing a non-empty bad set), on PROPER thin μ_n ⊊ F_p*, p prize-regime.
Construction: pick several "planted" scalars γ_i and low-degree codewords c_i; set
u0, u1 so that on a big agreement set, u0+γ_i u1 = c_i for each planted γ_i.
Simplest: u1 = a fixed low-deg codeword w; u0 = some word. Then u0+γ u1 is a codeword
on S iff u0 is a codeword on S (γ-independent) — too degenerate. 
Better: plant via 2 codewords. u0 = c_A (deg<k codeword), u1 = c_B (deg<k codeword).
Then u0+γ u1 = c_A+γ c_B is ALWAYS a deg<k codeword => EVERY γ is bad on the full set.
That over-saturates (every γ). Instead make u0,u1 codewords only on a SUBSET to get
finitely many bad γ with multiplicity > 1 (incidence > distinct).
"""
import itertools, random
from sympy import isprime, primitive_root

def find_p(n, beta=4):
    target = n**beta
    p = target + 1
    while True:
        if (p-1) % n == 0 and isprime(p):
            return p
        p += 1

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h,i,p) for i in range(n)})

def lowdeg_codeword(dom, k, p, coeffs):
    # poly of degree < k evaluated on dom
    return [sum(coeffs[e]*pow(x,e,p) for e in range(k)) % p for x in dom]

def residual_val(vals_u, tup, dom, k, p):
    xs=[dom[i] for i in tup]; ys=[vals_u[i] for i in tup]
    M=[[pow(xs[j],e,p) for e in range(k)]+[ys[j]] for j in range(k)]
    m=k
    for col in range(m):
        piv=None
        for r in range(col,m):
            if M[r][col]%p!=0: piv=r;break
        if piv is None: return 1
        M[col],M[piv]=M[piv],M[col]
        inv=pow(M[col][col],p-2,p)
        M[col]=[(v*inv)%p for v in M[col]]
        for r in range(m):
            if r!=col and M[r][col]%p!=0:
                f=M[r][col]; M[r]=[(M[r][i]-f*M[col][i])%p for i in range(m+1)]
    coeffs=[M[i][m]%p for i in range(m)]
    pred=sum(coeffs[e]*pow(xs[k],e,p) for e in range(k))%p
    return (pred-ys[k])%p

def analyze(n,k,a,beta,seed):
    p=find_p(n,beta); dom=mu_n(p,n); random.seed(seed)
    # Build u0,u1 as low-deg codewords on a planted agreement set T of size s (k+1<s<n),
    # random off T => forces bad gammas tied to the agreement structure on T.
    s = max(a, k+2)
    if s > n: s = n
    T = sorted(random.sample(range(n), s))
    cA = [random.randrange(p) for _ in range(k)]
    cB = [random.randrange(p) for _ in range(k)]
    fullA = lowdeg_codeword(dom,k,p,cA)
    fullB = lowdeg_codeword(dom,k,p,cB)
    u0=[random.randrange(p) for _ in range(n)]
    u1=[random.randrange(p) for _ in range(n)]
    for i in T:
        u0[i]=fullA[i]; u1[i]=fullB[i]
    idx=list(range(n))
    pinned=set(); alignable=set(); bad=set()
    for S in itertools.combinations(idx,a):
        all_t=list(itertools.combinations(S,k+1))
        cand=None; nd=False
        for t in all_t:
            r0=residual_val(u0,t,dom,k,p); r1=residual_val(u1,t,dom,k,p)
            if not (r0==0 and r1==0):
                nd=True
                if r1%p!=0: cand=(-r0*pow(r1,p-2,p))%p
                else: cand=None
                break
        if not nd or cand is None: continue
        good=True
        for t in all_t:
            r0=residual_val(u0,t,dom,k,p); r1=residual_val(u1,t,dom,k,p)
            if (r0+cand*r1)%p!=0: good=False;break
        if good:
            alignable.add(S); pinned.add(cand); bad.add(cand)
    return p,len(bad),len(pinned),len(alignable),s

print("n  k  a  s  p       #bad #pinned #alignable  bad==pinned  pinned<=incid (slack)")
for (n,k,a,beta) in [(8,2,4,4),(8,2,5,4),(8,2,6,4),(16,2,5,4),(16,2,6,4)]:
    for seed in [1,2,3]:
        p,nb,npn,nal,s=analyze(n,k,a,beta,seed)
        eq="YES" if nb==npn else f"NO({nb}v{npn})"
        rel="strict" if npn<nal else ("tight" if npn==nal else "BAD")
        print(f"{n:2} {k}  {a}  {s}  {p:6}  {nb:3}  {npn:4}   {nal:5}      {eq:6}    {rel} (excess {nal-npn})")
