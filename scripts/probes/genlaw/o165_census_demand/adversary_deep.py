# [MEASURED-FAITHFUL] Worst-case-over-stacks DEMAND-side count at the EXACT CensusDomination
# deep-band pin (kc=(r-2)m+1, a0=rm+1, m=1, n=16), faithful BabyBear. Adversarial stack search:
# monomial, random, mono-sum, coset-structured (P(x^d)), block-constant. Count #alignable a0-sets.
from math import comb
from itertools import combinations
import random
p = 2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,200):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def interp_coeffs(pts, vals):
    m=len(pts)
    A=[[pow(pts[i],j,p) for j in range(m)] for i in range(m)]
    M=[A[i][:]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        inv=pow(M[col][col],p-2,p); M[col]=[(v*inv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                f=M[rr][col]; M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]
def count_align(n,a,kc,dom,u0,u1):
    al=0; bad=set()
    for S in combinations(range(n), a):
        pts=[dom[i] for i in S]
        c0=interp_coeffs(pts,[u0[i] for i in S]); c1=interp_coeffs(pts,[u1[i] for i in S])
        if c0 is None or c1 is None: continue
        gam=None; ok=True; nd=False
        for j in range(kc,a):
            x0=c0[j]; x1=c1[j]
            if x0 or x1: nd=True
            if x1==0:
                if x0: ok=False; break
            else:
                g=(-x0*pow(x1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: ok=False; break
        if ok and nd:
            al+=1
            if gam is not None: bad.add(gam)
    return al,len(bad)
n=16; rng=random.Random(7)
print("=== [MEASURED-FAITHFUL] Worst-case stack search, n=16, deep band a0=rm+1, faithful BabyBear ===")
for r in [3,4,5]:
    kc=(r-2)+1; a0=r+1; dom=mu_n(n); K=(1<<r)*comb(n//2,r)
    best=-1; bestname=""
    # monomial-pair family: u0=x^e, u1=x^f for all e,f
    for e in range(n):
        for f in range(n):
            if e==f: continue
            u0=[pow(x,e,p) for x in dom]; u1=[pow(x,f,p) for x in dom]
            a,b=count_align(n,a0,kc,dom,u0,u1)
            if a>best: best=a; bestname=f"mono x^{e},x^{f}"
    mono_best=best; mono_name=bestname
    # KKH26 canonical
    u0=[pow(x,r,p) for x in dom]; u1=[pow(x,r-1,p) for x in dom]
    kkh,_=count_align(n,a0,kc,dom,u0,u1)
    # random stacks
    for _ in range(40):
        u0=[rng.randrange(p) for _ in range(n)]; u1=[rng.randrange(p) for _ in range(n)]
        a,b=count_align(n,a0,kc,dom,u0,u1)
        if a>best: best=a; bestname="random"
    # coset-structured P(x^d)
    for d in [2,4,8]:
        for _ in range(30):
            deg=rng.randint(1,n//d)
            cf=[rng.randrange(p) for _ in range(deg+1)]
            u0=[sum(cf[t]*pow(pow(x,d,p),t,p) for t in range(deg+1))%p for x in dom]
            u1=[pow(x,r-1,p) for x in dom]
            a,b=count_align(n,a0,kc,dom,u0,u1)
            if a>best: best=a; bestname=f"P(x^{d})"
    print(f" r={r} kc={kc} a0={a0}: KKH26-monomial-canonical={kkh}  mono-pair-max={mono_best} ({mono_name})  overall-max={best} ({bestname})  K={K}  -> max<=K? {best<=K}")
