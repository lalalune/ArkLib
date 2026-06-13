#!/usr/bin/env python3
"""#389: max_w |list| vs N_fib for s=8 (mu=3), all r, at GENERIC primes (n=8 << p^(2/3)).
Fast: s=8 means C(8,r) tiny. Decisive: p>8^4=4096 is generic."""
import itertools, random, sys
from math import comb
random.seed(7)

def subgroup(p, s):
    for h in range(2, p):
        g = pow(h, (p-1)//s, p); o, x = 1, g
        while x != 1: x = x*g % p; o += 1
        if o == s: return [pow(g, i, p) for i in range(s)]

def interp(pts, p):
    m = len(pts); poly = [0]*m
    for i,(xi,yi) in enumerate(pts):
        num=[1]; den=1
        for j,(xj,_) in enumerate(pts):
            if j==i: continue
            new=[0]*(len(num)+1)
            for k,c in enumerate(num): new[k]=(new[k]-c*xj)%p; new[k+1]=(new[k+1]+c)%p
            num=new; den=den*(xi-xj)%p
        cm=yi*pow(den,p-2,p)%p
        for k,c in enumerate(num): poly[k]=(poly[k]+cm*c)%p
    deg=-1
    for k in range(m-1,-1,-1):
        if poly[k]%p: deg=k; break
    return tuple(poly), deg

def list_size(mus,w,p,r,d):
    cw=set()
    for S in itertools.combinations(range(len(mus)),r):
        poly,deg=interp([(mus[i],w[i]) for i in S],p)
        if deg<=d: cw.add(poly[:d+1])
    return len(cw)

def nfib(mu,r): h=1<<(mu-1); return comb(h-(r%2), r//2)

def best(mus,p,r,d):
    n=len(mus); b=0; kind=""
    lams=set((-sum(mus[i] for i in S))%p for S in itertools.combinations(range(n),r))
    for lam in lams:
        w=[(pow(x,r,p)+lam*pow(x,r-1,p))%p for x in mus]
        v=list_size(mus,w,p,r,d)
        if v>b: b,kind=v,"ladder"
    for _ in range(2000):
        deg=random.randrange(1,n); cf=[random.randrange(p) for _ in range(deg+1)]
        w=[sum(cf[k]*pow(x,k,p) for k in range(deg+1))%p for x in mus]
        v=list_size(mus,w,p,r,d)
        if v>b: b,kind=v,f"poly deg{deg}"
    for _ in range(400):
        w=[random.randrange(p) for _ in range(n)]; cur=list_size(mus,w,p,r,d)
        for _s in range(150):
            i=random.randrange(n); o=w[i]; w[i]=random.randrange(p)
            nv=list_size(mus,w,p,r,d)
            if nv>=cur: cur=nv
            else: w[i]=o
        if cur>b: b,kind=cur,"climb"
    return b,kind

mu=3; s=8
print("s=8 (mu=3), n=8, all r, generic primes (n << p^(2/3)). N_fib & max_w |list|:", flush=True)
fails=0
for p in [12289, 65537, 40961, 114689, 147457]:
    if (p-1)%s: continue
    mus=subgroup(p,s); p23=int(p**(2/3))
    print(f"\np={p} (p^2/3~{p23}, n=8 in-regime):", flush=True)
    for r in range(2,5):
        nf=nfib(mu,r); mx,kind=best(mus,p,r,r-2)
        st="OK = N_fib" if mx==nf else (f"REFUTED > N_fib via {kind}" if mx>nf else f"< N_fib")
        if mx>nf: fails+=1
        print(f"  r={r}: N_fib={nf} max_w={mx}  [{st}]", flush=True)
print(f"\nREFUTATIONS: {fails}  (0 => N_fib exact for all r at s=8 generic)", flush=True)
