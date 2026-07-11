#!/usr/bin/env python3
"""
A9 EXCESS-ORBIT ANATOMY -- dissect the over-budget band's bad-gamma set (issue #407).

From the exact A2 scan, the UPPER bound on delta* is set by the DEEPEST band w_b whose
worst-direction incidence I exceeds budget=n. Observed (exact, q>>n^4, proper mu_n):
  n=8 rho=1/4: boundary w*=5 (I=8=n); the band JUST above, w=4 dir(4,7), I=9 = n+1
               (NON-divisible by orbit size S=8 -> NOT a clean orbit union).
  n=8 rho=1/2: boundary w*=6 (I=4); band above w=5 dir(4,5) I=40 = 5*n.

This probe ANATOMIZES the over-budget bad-gamma set at the boundary-defining band:
 (1) the bad-gamma set as a union of <zeta^{b-a}>-orbits (gamma -> gamma*zeta^{b-a});
     report #full orbits + size of any partial/fixed remainder.
 (2) the EXPLICIT consistent subsets realizing each bad gamma (coset content / tail).
 (3) test whether the excess (I - n) is a FIXED-POINT gamma (gamma with zeta^{b-a}-orbit
     of size 1, i.e. gamma=0 or a root that the dilation stabilizes) or a short orbit.
This determines whether a COSET-UNION witness alone can exceed n, or whether the excess
needs non-coset (generic-tail) subsets -> reduces to the open orbit count.

Exact char-0 via big prime q==1 mod n, q>>n^4, proper subgroup, moderate v2. Flushes.
"""
import itertools, sys
from math import gcd, log2

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x in (1,m-1): continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True; break
        if not ok: return False
    return True
def factor(x):
    f={}; d=2
    while d*d<=x:
        while x%d==0: f[d]=f.get(d,0)+1; x//=d
        d+=1
    if x>1: f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(factor(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def setup(n, plo, skip=0):
    p = plo + (1-plo)%n
    if p<plo: p+=n
    found=0
    while True:
        if isprime(p):
            v=p-1; v2=0
            while v%2==0: v//=2; v2+=1
            if v2 <= int(log2(n))+4:
                if found==skip:
                    g=proot(p); h=pow(g,(p-1)//n,p)
                    mu=[pow(h,i,p) for i in range(n)]
                    return p, mu, h
                found+=1
        p+=n

def make_member(p, mu, k):
    inv=lambda z: pow(z,p-2,p)
    invc={}
    def ddk(vals, idx):
        vs=list(vals)
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                key=(idx[i],idx[i-j]); d=invc.get(key)
                if d is None:
                    d=inv((mu[idx[i]]-mu[idx[i-j]])%p); invc[key]=d
                vs[i]=(vs[i]-vs[i-1])*d%p
        return vs[k]
    def in_RS(vals, idx):
        w=len(idx)
        if w<=k: return True
        for st in range(w-k):
            if ddk(vals[st:st+k+1], idx[st:st+k+1])!=0: return False
        return True
    return ddk, in_RS

def bad_gammas_with_subsets(a,b,n,mu,k,p,w,member):
    ddk,in_RS=member
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    inv=lambda z: pow(z,p-2,p)
    g2subs={}  # gamma -> list of subsets realizing it
    for R in itertools.combinations(range(n),w):
        idx=list(R)
        u1=[MUb[i] for i in R]
        if in_RS(u1,idx):
            continue
        u0=[MUa[i] for i in R]
        gm=None
        for st in range(w-k):
            a1=ddk(u1[st:st+k+1],idx[st:st+k+1])
            if a1%p:
                a0=ddk(u0[st:st+k+1],idx[st:st+k+1])
                gm=(-a0*inv(a1))%p; break
        if gm is None: continue
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(w)],idx):
            g2subs.setdefault(gm,[]).append(R)
    return g2subs

def orbit_decompose(gammas, step, n, h, p):
    """partition gammas into <zeta^step>-orbits: gamma -> gamma*h^step. report orbit sizes."""
    zs=pow(h,step,p)  # zeta^step
    remaining=set(gammas)
    orbits=[]
    while remaining:
        g=next(iter(remaining)); orb=[]; cur=g
        for _ in range(n):
            if cur in remaining:
                orb.append(cur); remaining.discard(cur)
            cur=(cur*zs)%p
            if cur==g: break
        orbits.append(orb)
    return orbits

def coset_content(S, n):
    """describe S: which antipodal cosets (mod n/2 pairing i ~ i+n/2) are full, tail points."""
    half=n//2
    pairs={i:(i,(i+half)%n) for i in range(half)}
    Sset=set(S)
    full=[]; tail=[]
    for i in range(half):
        a,b=pairs[i]
        if a in Sset and b in Sset: full.append((a,b))
        elif a in Sset: tail.append(a)
        elif b in Sset: tail.append(b)
    return full, tail

def main():
    print("="*84, flush=True)
    print("A9 EXCESS-ORBIT ANATOMY: structure of the over-budget bad-gamma set", flush=True)
    print("="*84, flush=True)
    # (n,k,w,dir) at the over-budget band just above the crossing
    cases=[(8,2,4,(4,7)),(8,2,4,(5,6)),(8,2,3,(2,3)),
           (8,4,5,(4,5)),(8,4,5,(5,6)),
           (8,2,5,(4,5)),(8,4,6,(4,6))]  # last two = boundary (I<=n) for contrast
    for (n,k,w,dirn) in cases:
        plo=max(200003,4*n**4+7)
        p,mu,h=setup(n,plo)
        member=make_member(p,mu,k)
        a,b=dirn; step=b-a; S=n//gcd(step,n)
        g2subs=bad_gammas_with_subsets(a,b,n,mu,k,p,w,member)
        gammas=list(g2subs.keys())
        I=len(gammas)
        orbits=orbit_decompose(gammas,step,n,h,p)
        osz=sorted(len(o) for o in orbits)
        print(f"\nn={n} k={k} dir=({a},{b}) step={step} w={w} delta={1-w/n:.4f} "
              f"budget=n={n}", flush=True)
        print(f"   I={I} [{'OVER' if I>n else 'ok'}]  orbit-size S=n/gcd={S}  "
              f"#orbits={len(orbits)} orbit-sizes={osz}", flush=True)
        # excess analysis
        nfull=sum(1 for o in orbits if len(o)==S)
        partial=[len(o) for o in orbits if len(o)!=S]
        print(f"   decomposition: {nfull} FULL orbits (size {S}) + partials {partial}  "
              f"=> I = {nfull}*{S} + {sum(partial)} = {nfull*S+sum(partial)}", flush=True)
        # show coset content of subsets for a couple of gammas
        for gi,g in enumerate(gammas[:3]):
            subs=g2subs[g]
            descs=[]
            for Sset in subs[:2]:
                full,tail=coset_content(Sset,n)
                descs.append(f"S={Sset} fullcosets={len(full)} tail={tail}")
            print(f"      gamma#{gi}: realized by {len(subs)} subsets; e.g. {descs}", flush=True)
    print("\nDONE", flush=True)

if __name__=="__main__":
    main()
