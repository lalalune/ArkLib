#!/usr/bin/env python3
"""
A9 FIXED-POINT EXCESS check (#407): is the over-budget '+1' at n=8,k=2,w=4,dir(4,7)
the gamma=0 fixed point of the dilation gamma->gamma*zeta^{b-a}?  gamma=0 means x^a alone
agrees with deg<k poly on the w-subset (x^b coefficient irrelevant). Verify the size-1
orbit gamma value == 0, and whether x^a in RS[k] on its realizing subset.
Exact char-0, big prime, proper mu_n.
"""
import itertools
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
def setup(n,plo):
    p=plo+(1-plo)%n
    if p<plo: p+=n
    while True:
        if isprime(p):
            v=p-1;v2=0
            while v%2==0: v//=2;v2+=1
            if v2<=int(log2(n))+4:
                g=proot(p);h=pow(g,(p-1)//n,p)
                return p,[pow(h,i,p) for i in range(n)],h
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

n,k,w,a,b=8,2,4,4,7
p,mu,h=setup(n,max(200003,4*n**4+7))
ddk,in_RS=make_member(p,mu,k)
MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
inv=lambda z:pow(z,p-2,p)
g2subs={}
for R in itertools.combinations(range(n),w):
    idx=list(R);u1=[MUb[i] for i in R]
    if in_RS(u1,idx): continue
    u0=[MUa[i] for i in R];gm=None
    for st in range(w-k):
        a1=ddk(u1[st:st+k+1],idx[st:st+k+1])
        if a1%p:
            a0=ddk(u0[st:st+k+1],idx[st:st+k+1]);gm=(-a0*inv(a1))%p;break
    if gm is None: continue
    if in_RS([(u0[i]+gm*u1[i])%p for i in range(w)],idx):
        g2subs.setdefault(gm,[]).append(R)
print(f"n={n} k={k} dir=({a},{b}) w={w} I={len(g2subs)}",flush=True)
print(f"  gamma=0 present? {0 in g2subs}",flush=True)
if 0 in g2subs:
    for R in g2subs[0]:
        u0=[MUa[i] for i in R]
        print(f"    gamma=0 subset {R}: x^a in RS[k] on R = {in_RS(u0,list(R))}",flush=True)
# size of dilation orbit per gamma
zs=pow(h,b-a,p)
sizes={}
for g in g2subs:
    cur=g;c=0
    for _ in range(n+1):
        c+=1;cur=(cur*zs)%p
        if cur==g: break
    sizes[g]=c
from collections import Counter
print(f"  orbit-size multiset of bad gammas: {dict(Counter(sizes.values()))}",flush=True)
print(f"  the size-1 (fixed) gammas: {[g for g,s in sizes.items() if s==1]} (0 is fixed by any dilation)",flush=True)
