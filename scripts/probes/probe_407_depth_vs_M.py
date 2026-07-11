#!/usr/bin/env python3
"""
#407 -- does ODD zero-sum Sidon DEPTH d_odd(n,p) (first odd r with W_r>0) control M=max|eta_b|?
The thinness-essential finding: d_odd GROWS with beta (thin => deeper). For a LEVER we need:
deeper d_odd  =>  smaller normalized M = M/sqrt(n log(p/n))  (the prize ratio). Test the
correlation HONESTLY across many (p) at fixed n, mixing thick & thin, and ask:
is M/sqrt(n log(p/n)) MONOTONE in d_odd, or does depth NOT translate to a sup bound?

If NO monotone control: depth is a true thinness invariant but NON-PROVING for M (like the
rigid -n^r identity) -> a mapped constraint, honest wall. If monotone: live bootstrap edge.
"""
import math
def is_prime(n):
    if n<2:return False
    if n%2==0:return n==2
    d=3
    while d*d<=n:
        if n%d==0:return False
        d+=2
    return True
def factor(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def prim(p):
    fac=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def find_primes(target,n,count,odd_m=True):
    out=[];k0=max(1,round(target/n))
    for d in range(0,4000000):
        for s in(1,-1):
            kk=k0+s*d
            if kk<1:continue
            p=kk*n+1
            if p>3 and is_prime(p):
                if odd_m and ((p-1)//n)%2==0:continue
                if p not in out:out.append(p)
            if len(out)>=count:return out
    return out
def subgroup(n,p):
    g=prim(p);h=pow(g,(p-1)//n,p);e=[];x=1
    for _ in range(n):e.append(x);x=x*h%p
    return e
def Wr(elts,p,r):
    cur=[0]*p
    for x in elts:cur[x%p]+=1
    for _ in range(r-1):
        nxt=[0]*p
        for t in range(p):
            c=cur[t]
            if c:
                for x in elts:nxt[(t+x)%p]+=c
        cur=nxt
    return cur[0]
def Mmax(elts,p):
    w=2*math.pi/p;best=0.0
    for b in range(1,p):
        s=0.0;im=0.0
        for x in elts:
            a=w*((b*x)%p);s+=math.cos(a);im+=math.sin(a)
        v=math.hypot(s,im)
        if v>best:best=v
    return best
def run():
    n=16;log2n=4
    print(f"n={n}: depth d_odd (first odd r, W_r>0) vs normalized M/sqrt(n*log(p/n)).")
    print("Lever needs: deeper d_odd => smaller normalized M (monotone). Else non-proving.\n")
    rows=[]
    for beta in [2.3,2.6,2.9,3.2,3.6,4.0,4.6]:
        for p in find_primes(int(n**beta),n,2):
            e=subgroup(n,p)
            d_odd=next((r for r in range(3,16,2) if Wr(e,p,r)>0),99)
            M=Mmax(e,p)
            rb=math.log(p)/math.log(n)
            norm=M/math.sqrt(n*math.log(p/n))
            rows.append((rb,p,d_odd,M,norm))
    rows.sort()
    print(f"  {'beta':>5} {'p':>8} {'d_odd':>6} {'M':>7} {'M/sqrt(n ln(p/n))':>18}")
    for rb,p,d,M,no in rows:
        print(f"  {rb:5.2f} {p:8d} {d:6d} {M:7.2f} {no:18.4f}")
if __name__=="__main__":
    run()
