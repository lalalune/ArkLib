#!/usr/bin/env python3
"""
probe_dsval_mann_n16n32_worst.py  (#407 A5 -- worst-direction-only delta* for n=16,32)

The exact char-0 ground truth (issue + our n=8 reproduction) shows the worst far
direction is of the form (a,b) with a = n/2 (the antipodal-coset generator) and b
just above a.  We restrict to a SMALL set of worst-candidate directions and compute
I(w) and delta* EXACTLY (p>>n^4) with a fast structural max-agreement that uses the
Mann coset+tail structure: max agreement = max over (anchor = k pts) but anchors
restricted to coset-aligned families + a randomized adversarial sweep (exact on the
realized witnesses; reported as LOWER bound on I, which only makes delta* an UPPER
bound -- but we cross-check the n=16 issue values to confirm tightness).

Goal: extract w_min(n,k) and the closed form for delta*(n,rho).
"""
import itertools,random
from math import log2

def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,lo):
    p=lo+(n-(lo%n))+1
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=n
def prim_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def rou(p,n):
    g=prim_root(p);w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]
def v2(x):
    if x==0:return 99
    c=0
    while x%2==0:x//=2;c+=1
    return c

def fast_max_agreement(mu,a,b,gamma,k,p,n,extra_anchors=1200):
    idxs=list(range(n))
    h=[(pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p for i in idxs]
    best=0
    anchors=set()
    # coset-aligned: arithmetic progressions of dyadic steps
    for step in [1,2,4,8,16]:
        for start in range(n):
            anc=tuple(sorted((start+j*step)%n for j in range(k)))
            if len(set(anc))==k:anchors.add(anc)
    # antipodal-pair-built anchors: take pairs {i,i+n/2}
    half=n//2
    pairs=[(i,(i+half)%n) for i in range(half)]
    for _ in range(extra_anchors):
        random.shuffle(pairs)
        chosen=[]
        for (i,j) in pairs:
            if len(chosen)+2<=k: chosen+=[i,j]
            else: break
        while len(chosen)<k:
            r=random.randrange(n)
            if r not in chosen: chosen.append(r)
        anchors.add(tuple(sorted(chosen[:k])))
    for _ in range(extra_anchors):
        anchors.add(tuple(sorted(random.sample(idxs,k))))
    for anchor in anchors:
        xs=[mu[i] for i in anchor];ys=[h[i] for i in anchor]
        cnt=0
        for i in idxs:
            tot=0;x=mu[i]
            for t in range(k):
                num=ys[t];den=1
                for s in range(k):
                    if s==t:continue
                    num=num*((x-xs[s])%p)%p;den=den*((xs[t]-xs[s])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            if tot==h[i]:cnt+=1
        if cnt>best:best=cnt
    return best

def candidate_gammas(mu,a,b,k,p,n,cap=20000):
    gset=set()
    cnt=0
    for T in itertools.combinations(range(n),k+1):
        xs=[mu[i] for i in T];c=[]
        for i in range(k+1):
            den=1
            for j in range(k+1):
                if j==i:continue
                den=den*((xs[i]-xs[j])%p)%p
            c.append(pow(den,p-2,p))
        La=sum(c[i]*pow(xs[i],a,p) for i in range(k+1))%p
        Lb=sum(c[i]*pow(xs[i],b,p) for i in range(k+1))%p
        if Lb==0:continue
        gset.add((-La*pow(Lb,p-2,p))%p)
        cnt+=1
        if len(gset)>cap:break
    return gset

def main():
    random.seed(7)
    gt={(16,4):0.5625,(16,8):0.3125}
    cases=[(16,4),(16,8),(32,8),(32,16)]
    rows=[]
    for (n,k) in cases:
        rho=k/n;p=find_prime(n,n**4*4);mu=rou(p,n)
        budget=n;half=n//2
        # worst-candidate directions: a in {half, half/2}, b in (a, a+small] and a+half-ish
        cand_a=sorted(set([half,half//2,k]))
        dirs=set()
        for a in cand_a:
            if a<k: continue
            for b in range(a+1,min(a+6,n)):
                dirs.add((a,b))
            for b in [a+half if a+half<n else None, n-1]:
                if b and b>a: dirs.add((a,b))
        results={}
        for (a,b) in sorted(dirs):
            gs=candidate_gammas(mu,a,b,k,p,n)
            print(f"   [dir({a},{b}) #candgamma={len(gs)}]",flush=True)
            gma={g:fast_max_agreement(mu,a,b,g,k,p,n) for g in gs}
            for w in range(k+1,n+1):
                c=sum(1 for g,m in gma.items() if m>=w)
                if w not in results or c>results[w][0]:
                    results[w]=(c,(a,b))
        ws=sorted(results)
        w_min=next((w for w in ws if results[w][0]<=budget),None)
        ds=1-w_min/n if w_min else None
        g=gt.get((n,k))
        print(f"\n=== n={n} k={k} rho={rho} p={p} dirs={sorted(dirs)} ===")
        for w in sorted(results,reverse=True):
            cc,d=results[w]
            if cc>0:
                mk=" <==" if w==w_min else ""
                print(f"   w={w:2d} d={1-w/n:.4f} I={cc:4d} dir={d}{mk}")
        print(f"  delta*={ds} gt={g} MATCH={(abs(ds-g)<1e-9) if (g and ds) else '?'}")
        if w_min:
            print(f"  w_min={w_min} n-w_min={n-w_min} w_min-k={w_min-k}")
        rows.append((n,k,rho,w_min,ds,g))
    print("\n===== TABLE =====")
    print(" n  k  rho   w_min  n-w_min  delta*    gt      1-rho-1/n  1-rho-2/n  1-rho-3/n")
    for (n,k,rho,w_min,ds,g) in rows:
        if w_min:
            print(f"{n:3d}{k:3d} {rho:4.2f}  {w_min:4d}   {n-w_min:5d}  {ds:.4f}  {g}   {1-rho-1/n:.4f}    {1-rho-2/n:.4f}    {1-rho-3/n:.4f}")

if __name__=="__main__":
    main()
