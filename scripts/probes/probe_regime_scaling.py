#!/usr/bin/env python3
"""
REGIME-SCALING: does designed-q let B/sqrt(n) stay O(1), or does it grow with q/n?

Fix n=2^mu.  Over q=p^2 (exact, fast GF(p^2)), grow p.  Track:
  B/sqrt(n)              (Ramanujan ratio; target O(1), ideally <=2)
  B/sqrt(n*log(q/n))     (the MEASURED-true scaling; if -> const, B ~ sqrt(n log(q/n)))
  B/sqrt(q)              (vacuous-wall ratio; -> 0 means we beat Weil)
and the MINIMUM over many p (the BEST designed q at each size).

KEY: we separate q=p^2 into two arithmetic classes and compare BEST B/sqrt(n):
  class A: n | (p-1)  (mu_n lives in prime subfield F_p)  -- "split" / spike-prone
  class B: n | (p+1)  (mu_n in norm-1 torus)              -- "inert-ish"
  class C: neither (n | p^2-1 only, ord_n(p)=2 genuinely) -- "generic"
We want to know if ANY class gives B/sqrt(n) bounded as q grows.  If B/sqrt(n) ~ sqrt(log(q/n))
in ALL classes, then NO designed-q beats sqrt(n) by more than a sqrt-log -- i.e. the
2-power designed family is Ramanujan-up-to-sqrt-log, and the prize bound B<=C sqrt(n log(q/n))
is TIGHT and achieved by the whole family (good news), but the clean 2 sqrt(n) is NOT achievable.
"""
import cmath, math, random
from collections import Counter

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f
def qnr(p):
    for u in range(2,p):
        if pow(u,(p-1)//2,p)==p-1: return u
    raise RuntimeError
def gf2_mul(x,y,u,p):
    a,b=x;c,d=y; return ((a*c+b*d*u)%p,(a*d+b*c)%p)
def gf2_pow(x,e,u,p):
    r=(1,0)
    while e>0:
        if e&1: r=gf2_mul(r,x,u,p)
        x=gf2_mul(x,x,u,p); e>>=1
    return r
def find_gen_gf2(p,u):
    order=p*p-1; pf=list(factorize(order).keys())
    # try small structured candidates first for speed, then sweep
    cands=[(0,1),(1,1),(2,1),(3,1),(1,2),(2,3)] + [(a,b) for a in range(p) for b in range(1,p)]
    for g in cands:
        if all(gf2_pow(g,order//pr,u,p)!=(1,0) for pr in pf): return g
    raise RuntimeError
def gauss_B(p,n):
    order=p*p-1; u=qnr(p); g=find_gen_gf2(p,u); k=order//n
    exp_t=[None]*order; cur=(1,0)
    for i in range(order): exp_t[i]=cur; cur=gf2_mul(cur,g,u,p)
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p; mx=0.0
    for c in range(k):
        bc=exp_t[c%order]; s=0j
        for y in mu: prod=gf2_mul(bc,y,u,p); s+=cmath.exp(1j*w*(2*prod[0]%p))
        a=abs(s)
        if a>mx: mx=a
    return mx,k

def classof(p,n):
    if (p-1)%n==0: return 'A_split'
    if (p+1)%n==0: return 'B_inert'
    return 'C_generic'

if __name__=="__main__":
    random.seed(11)
    for n in [8,16,32]:
        print(f"\n############ n={n}=2^{int(math.log2(n))} ############")
        print(f"{'p':>6} {'q':>9} {'class':>9} {'B':>9} {'B/sqrtn':>8} {'B/sqrt(n*log(q/n))':>19} {'B/sqrtq':>8} {'log(q/n)':>9}")
        rows=[]
        plist=[]
        pp=3
        while len(plist)<40 and pp< 100000:
            if is_prime(pp) and (pp*pp-1)%n==0: plist.append(pp)
            pp+=2
        # subsample geometrically to cover a wide q range
        idx=sorted(set(int(round(x)) for x in
                       [i for i in range(min(18,len(plist)))] +
                       [int(len(plist)*f) for f in (0.5,0.6,0.7,0.8,0.9,0.97)]))
        idx=[i for i in idx if i<len(plist)]
        for i in idx:
            p=plist[i]
            B,k=gauss_B(p,n)
            q=p*p; cls=classof(p,n); lqn=math.log(q/n)
            r1=B/math.sqrt(n); r2=B/math.sqrt(n*lqn) if lqn>0 else float('nan')
            rows.append((p,q,cls,B,r1,r2,B/math.sqrt(q),lqn))
            print(f"{p:>6} {q:>9} {cls:>9} {B:>9.3f} {r1:>8.3f} {r2:>19.3f} {B/math.sqrt(q):>8.4f} {lqn:>9.3f}")
        # best (min B/sqrtn) per class
        print("  -- BEST (min B/sqrtn) and trend per class --")
        for cls in ('A_split','B_inert','C_generic'):
            cr=[r for r in rows if r[2]==cls]
            if not cr: continue
            cr_sorted=sorted(cr,key=lambda r:r[4])
            best=cr_sorted[0]; worst=cr_sorted[-1]
            # does B/sqrt(n log(q/n)) stabilize?  report range of r2
            r2s=[r[5] for r in cr]
            print(f"   {cls}: min B/sqrtn={best[4]:.3f} (p={best[0]}); max={worst[4]:.3f} (p={worst[0]}); "
                  f"B/sqrt(n log(q/n)) in [{min(r2s):.3f},{max(r2s):.3f}]")
