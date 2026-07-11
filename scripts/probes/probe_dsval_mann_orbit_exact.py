#!/usr/bin/env python3
"""
probe_dsval_mann_orbit_exact.py  (#407 A5 -- EXACT delta* via agreement-set->gamma->orbit)

EFFICIENT EXACT route (p>>n^4).  Instead of sweeping gammas, we enumerate AGREEMENT
SETS S directly and, for each, find the gamma(s) that make x^a+gamma x^b deg<k-
interpolable on S.  The distinct-gamma count I(w) = #{ gamma : exists |S|>=w with
gamma consistent on S }.  By the orbit-closure law (badSet_orbit_closed) the bad
gammas for a fixed direction come in orbits under gamma->gamma*w^{b-a}; we just count
the realized gammas directly.

Per direction (a,b), per agreement set S (|S|=w):
  gamma consistent on S  <=>  there is deg<k g with x^a+gamma x^b=g on S.
  Linear system in (c_0..c_{k-1}, gamma).  Solve EXACTLY (Gaussian over F_p):
   - returns a unique gamma, OR 'all' (degenerate), OR empty.
We restrict S to the MANN-STRUCTURED + TAIL family that the reconcile probe proved
is extremal:
   S = (a union B of antipodal pairs {i,i+n/2})  union  (tail T of size tau in {0,1,2}),
   T unpaired.  This is exactly Mann's decomposition: paired block + bounded tail.
We enumerate ALL such S of each size w (feasible: pairs choose subsets + small tail),
collect the realized gammas, and read I(w) and delta*=sup{delta: I<=n}.

We VALIDATE against n=8 (gt 0.375 / 0.25) and n=16 (gt 0.5625 / 0.3125) and then
EXTRAPOLATE to n=32,64 to pin the closed form.
"""
import itertools
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

def gamma_for_S(mu,a,b,S,k,p):
    """unique gamma s.t. x^a+gamma x^b deg<k-interpolable on S, or None, or 'all'."""
    Sl=sorted(S);w=len(Sl)
    if w<=k: return 'all'
    nvar=k+1   # c_0..c_{k-1}, gamma
    aug=[]
    for i in Sl:
        x=mu[i]
        row=[pow(x,j,p) for j in range(k)]+[(-pow(x,b,p))%p]+[pow(x,a,p)]
        aug.append(row)
    r=0;pivcol=[]
    for c in range(nvar):
        piv=None
        for ii in range(r,w):
            if aug[ii][c]%p!=0:piv=ii;break
        if piv is None:continue
        aug[r],aug[piv]=aug[piv],aug[r]
        inv=pow(aug[r][c],p-2,p)
        aug[r]=[(x*inv)%p for x in aug[r]]
        for ii in range(w):
            if ii!=r and aug[ii][c]%p!=0:
                f=aug[ii][c];aug[ii]=[(aug[ii][j]-f*aug[r][j])%p for j in range(nvar+1)]
        pivcol.append(c);r+=1
        if r==w:break
    for ii in range(r,w):
        if aug[ii][nvar]%p!=0 and all(aug[ii][j]%p==0 for j in range(nvar)):
            return None
    if k in pivcol:
        prow=pivcol.index(k)
        freecols=[c for c in range(nvar) if c not in pivcol]
        if any(aug[prow][c]%p!=0 for c in freecols):
            return 'all'
        return aug[prow][nvar]%p
    else:
        return 'all'

def enumerate_S(n,max_tail=3):
    """Mann coset+tail agreement sets: B = union of antipodal pairs, T = small unpaired tail."""
    half=n//2
    pairs=[(i,i+half) for i in range(half)]
    out=[]
    # choose any subset of pairs (block B), plus a tail T of size 0..max_tail of singletons
    # tail singletons must NOT have their antipode in B or T (unpaired)
    # enumerate block sizes via bitmask over pairs (2^half) -- ok for half<=16 (n<=32: 2^16=65536)
    for bmask in range(1<<half):
        B=set()
        usedpair=set()
        for j in range(half):
            if bmask&(1<<j):
                B.add(pairs[j][0]);B.add(pairs[j][1]);usedpair.add(j)
        # tail: pick from pairs NOT in B, choose one endpoint, up to max_tail, no two from same pair both
        avail=[j for j in range(half) if j not in usedpair]
        # tail elements: choose subset of avail pairs, one endpoint each, size<=max_tail
        for tau in range(0,max_tail+1):
            for chosen in itertools.combinations(avail,tau):
                for ends in itertools.product([0,1],repeat=tau):
                    T=set(pairs[chosen[t]][ends[t]] for t in range(tau))
                    S=frozenset(B|T)
                    if len(S)>0: out.append((S,tau))
    return out

def deltastar(n,k,p,mu,dirs,max_tail=3):
    budget=n
    Slist=enumerate_S(n,max_tail)
    results={}   # w->(I,dir)
    for (a,b) in dirs:
        gammaset_by_w={}  # w -> set of gammas
        gamma_maxw={}
        for (S,tau) in Slist:
            w=len(S)
            if w<=k: continue
            g=gamma_for_S(mu,a,b,S,k,p)
            if g=='all' or g is None: continue
            if g not in gamma_maxw or w>gamma_maxw[g]:
                gamma_maxw[g]=w
        for w in range(k+1,n+1):
            c=sum(1 for g,mw in gamma_maxw.items() if mw>=w)
            if w not in results or c>results[w][0]:
                results[w]=(c,(a,b))
    ws=sorted(results)
    w_min=next((w for w in ws if results[w][0]<=budget),None)
    ds=1-w_min/n if w_min else None
    return results,w_min,ds

def main():
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    # (n,k, max_tail)
    import os
    if os.environ.get("BIG"):
        cases=[(32,8,2),(32,16,2)]
    else:
        cases=[(8,2,3),(8,4,3),(16,4,3),(16,8,3)]
    rows=[]
    for (n,k,mt) in cases:
        rho=k/n;p=find_prime(n,n**4*4);mu=rou(p,n)
        half=n//2
        # worst-candidate directions: a in {half, half/2, k}, b just above + antipodal
        cand=sorted(set([x for x in [half,half//2,k,k+1] if k<=x<n]))
        dirs=set()
        for a in cand:
            for b in range(a+1,min(a+4,n)):dirs.add((a,b))
            ab=a+half
            if ab<n: dirs.add((a,ab))
        dirs=sorted(dirs)
        results,w_min,ds=deltastar(n,k,p,mu,dirs,mt)
        g=gt.get((n,k))
        print(f"\n=== n={n} k={k} rho={rho} p={p} maxtail={mt} dirs={dirs} ===",flush=True)
        for w in sorted(results,reverse=True):
            cc,d=results[w]
            if cc>0:
                mk=" <==" if w==w_min else ""
                print(f"   w={w:2d} d={1-w/n:.4f} I={cc:5d} dir={d}{mk}")
        print(f"  delta*={ds} gt={g} MATCH={(abs(ds-g)<1e-9) if (g and ds) else '?'}")
        if w_min: print(f"  w_min={w_min} n-w_min={n-w_min} w_min-k={w_min-k}")
        rows.append((n,k,rho,w_min,ds,g))
    print("\n===== TABLE =====",flush=True)
    print(" n  k  rho   w_min  n-w_min  delta*    gt      1-rho-1/n  1-rho-2/n  half/n+? ")
    for (n,k,rho,w_min,ds,g) in rows:
        if w_min:
            print(f"{n:3d}{k:3d} {rho:4.2f}  {w_min:4d}   {n-w_min:5d}  {ds:.4f}  {g}   {1-rho-1/n:.4f}    {1-rho-2/n:.4f}  w_min-k={w_min-k}")

if __name__=="__main__":
    main()
