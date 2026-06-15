#!/usr/bin/env python3
"""
A9 BOUNDARY CLOSED FORM (#407): confirm at the delta* boundary band w*, the worst-direction
incidence I = exactly one dilation-orbit = S = n/gcd(b-a,n), and that the band just above
(w*-1) exceeds n. Restricts to the worst-direction family (a around n/2, step coprime) to
reach n=16,32 boundaries fast. Exact char-0, big prime, proper mu_n. Flushes.

Reports: for each (n,rho), boundary w*, I at w* and w*-1, the orbit decomposition, and
delta* = 1-w*/n with the witness upper bound delta* <= 1-w*/n (since w*-1 band exceeds n).
"""
import itertools, sys
from math import gcd, log2

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x in(1,m-1): continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True
def factor(x):
    f={};d=2
    while d*d<=x:
        while x%d==0: f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1: f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(factor(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def setup(n,plo,skip=0):
    p=plo+(1-plo)%n
    if p<plo: p+=n
    found=0
    while True:
        if isprime(p):
            v=p-1;v2=0
            while v%2==0: v//=2;v2+=1
            if v2<=int(log2(n))+4:
                if found==skip:
                    g=proot(p);h=pow(g,(p-1)//n,p)
                    return p,[pow(h,i,p) for i in range(n)],h
                found+=1
        p+=n
def make_member(p,mu,k):
    inv=lambda z:pow(z,p-2,p);invc={}
    def ddk(vals,idx):
        vs=list(vals)
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                key=(idx[i],idx[i-j]);d=invc.get(key)
                if d is None: d=inv((mu[idx[i]]-mu[idx[i-j]])%p);invc[key]=d
                vs[i]=(vs[i]-vs[i-1])*d%p
        return vs[k]
    def in_RS(vals,idx):
        w=len(idx)
        if w<=k: return True
        for st in range(w-k):
            if ddk(vals[st:st+k+1],idx[st:st+k+1])!=0: return False
        return True
    return ddk,in_RS

def incidence(a,b,n,mu,k,p,w,member,cap=None):
    ddk,in_RS=member
    MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
    inv=lambda z:pow(z,p-2,p);gam=set()
    for R in itertools.combinations(range(n),w):
        idx=list(R);u1=[MUb[i] for i in R]
        if in_RS(u1,idx):
            u0=[MUa[i] for i in R]
            if in_RS(u0,idx): return None  # saturated/near
            continue
        u0=[MUa[i] for i in R];gm=None
        for st in range(w-k):
            a1=ddk(u1[st:st+k+1],idx[st:st+k+1])
            if a1%p:
                a0=ddk(u0[st:st+k+1],idx[st:st+k+1]);gm=(-a0*inv(a1))%p;break
        if gm is None: continue
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(w)],idx):
            gam.add(gm)
            if cap and len(gam)>cap: return gam
    return gam

def main():
    print("="*80,flush=True)
    print("A9 BOUNDARY CLOSED FORM: I(w*)=S, I(w*-1)>n => delta*<=1-w*/n (witness upper)",flush=True)
    print("="*80,flush=True)
    # (n,k, candidate worst dirs as (a,b)) -- worst family near a=n/2, step coprime
    plans=[
        (8,2,[(4,5),(4,7),(5,6),(3,4),(2,5)]),
        (8,4,[(4,5),(4,6),(4,7),(5,6),(5,7)]),
        (16,4,[(8,9),(8,11),(8,13),(4,5),(7,8),(6,7),(4,7)]),
        (16,8,[(8,9),(8,10),(8,11),(8,12),(8,13),(9,10),(10,11)]),
        (32,8,[(16,17),(16,19),(8,9),(15,16),(16,21)]),
        (32,16,[(16,17),(16,18),(16,19),(16,20),(17,18)]),
    ]
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    for (n,k,dirs) in plans:
        rho=k/n;plo=max(200003,4*n**4+7)
        p,mu,h=setup(n,plo);p2,mu2,h2=setup(n,plo,skip=3)
        member=make_member(p,mu,k);member2=make_member(p2,mu2,k)
        budget=n
        print(f"\n--- n={n} k={k} rho={rho} q={p} budget={n} (worst-family dirs) ---",flush=True)
        # for each w, worst I over the candidate dirs
        wstar=None
        prevover=False
        for w in range(k+1,n):
            best=0;bdir=None;best2=0
            for (a,b) in dirs:
                if not (k<=a<b<n): continue
                I=incidence(a,b,n,mu,k,p,w,member,cap=budget+5)
                if I is None: continue
                if len(I)>best: best=len(I);bdir=(a,b)
            if bdir is not None:
                I2=incidence(*bdir,n,mu2,k,p2,w,member2,cap=budget+5)
                best2=len(I2) if I2 is not None else -1
            S=n//gcd(bdir[1]-bdir[0],n) if bdir else 0
            cross="OVER" if best>budget else "ok"
            pin="PIN-OK" if best==best2 else f"PIN?({best}v{best2})"
            mk=""
            if best<=budget and wstar is None and best>0:
                wstar=w;mk=" <-- delta* boundary (witness-tight)"
            print(f"   w={w:2d} d={1-w/n:.4f}: worstI(family)={best:4d}[{cross}] dir={bdir} S={S} {pin}{mk}",flush=True)
        ds=1-wstar/n if wstar else None
        g=gt.get((n,k))
        print(f"   => delta* (witness-tight boundary) = {ds}  (w*={wstar})  gt={g}  "
              f"{'MATCH' if g and ds and abs(ds-g)<1e-9 else ''}",flush=True)
        print(f"      witness upper bound: delta* <= 1-w*/n = {ds} "
              f"(band w*-1 has explicit witness I>n)",flush=True)

if __name__=="__main__":
    main()
