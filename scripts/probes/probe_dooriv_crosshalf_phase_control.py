#!/usr/bin/env python3
"""
door-(iv) cross-half phase CONTROLS — lock the mechanism:
(1) Is arg(B/A)=0 (real collinear) FORCED at the worst b*?  (mu_{n/2} negation-stable => A,B real => ratio real)
(2) Does |B|/|A| have genuine b-variance across the TOP BAND (so B is NOT a fixed phase-rotate of A)?
    Report at worst b* and the spread (min..max, std) of |B|/|A| over the top sqrt(m) frequencies.
EXACT C, proper 2-power mu_n, p>>n^3, full F_p* scan at n=16, sampled larger. NEVER n=q-1.
"""
import cmath, math, random, statistics
def isp(x):
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return x>1
def factor_small(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f
def primitive_root(p):
    fs=factor_small(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def gen_mu(p,n):
    g=primitive_root(p); return pow(g,(p-1)//n,p), g
def run(p,n,full,samples=6000):
    w=2*math.pi/p; EP=lambda t: cmath.exp(1j*w*(t%p))
    gen_n,g=gen_mu(p,n); m=(p-1)//n; half=n//2
    z=pow(gen_n,2,p); sub=[]; cur=1
    for _ in range(half): sub.append(cur); cur=cur*z%p
    reps=[]
    if full or m<=samples:
        cur=1
        for _ in range(m): reps.append(cur); cur=cur*g%p
    else:
        S=set()
        while len(reps)<samples:
            j=random.randrange(m)
            if j in S: continue
            S.add(j); reps.append(pow(g,j,p))
    rows=[]
    for b in reps:
        A=sum(EP((b*s)%p) for s in sub)
        B=sum(EP((b*gen_n*s)%p) for s in sub)
        rows.append((abs(A+B),A,B))
    rows.sort(key=lambda r:-r[0])
    # worst b*
    mag0,A0,B0=rows[0]
    arg0=cmath.phase(B0/A0) if abs(A0)>1e-9 else None
    # top sqrt(m) band ratio spread
    topk=max(8,int(math.sqrt(len(rows))))
    ratios=[]; args=[]
    for mag,A,B in rows[:topk]:
        if abs(A)<1e-9: continue
        ratios.append(abs(B)/abs(A)); args.append(abs(cmath.phase(B/A)))
    return m, mag0/math.sqrt(n), arg0, min(ratios),max(ratios),statistics.mean(ratios),statistics.pstdev(ratios), max(args), topk
PR={16:[65537,188417,1179649],32:[163841,1179649],64:[401537,786433]}
print("worst-b cross-half: arg(B*/A*) (rad), and |B|/|A| spread over top-√m band")
for n in (16,32,64):
    for p in PR[n]:
        if not isp(p) or (p-1)%n: continue
        full=(n==16)
        m,mag0,arg0,rmin,rmax,rmean,rstd,argmax,topk=run(p,n,full)
        tag="FULL" if full else "samp"
        print(f" n={n:2} p={p:8} m={m:6} [{tag}] worst|eta|/√n={mag0:.3f} arg(B*/A*)={arg0:+.2e}  |B|/|A| top-{topk}: [{rmin:.3f},{rmax:.3f}] mean={rmean:.3f} std={rstd:.3f} maxarg={argmax:.2e}")
