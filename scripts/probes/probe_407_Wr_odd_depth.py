#!/usr/bin/env python3
"""
#407 -- exact ODD-r zero-sum count W_r(mu_n, p) = #ordered r-tuples in mu_n summing to 0 mod p.
Confirms: to Sidon depth, W_r=0 for odd r => sum_{b!=0} eta_b^r = -n^r EXACTLY (p-independent).
Maps WHERE W_r first turns nonzero (odd r) and whether that onset is thinness-essential.

Honesty: pure integer convolution. Proper subgroups mu_n<F_p*, odd m=(p-1)/n preferred.
The constraint: A_r := sum_{b!=0} eta_b^r = p*W_r - n^r  (exact orthogonality, eta real).
Odd-r: if W_r=0 then A_r=-n^r (rigid). Onset of W_r>0 = additive depth = candidate thinness axis.
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
def find_prime(target,n,odd_m=True):
    k0=max(1,round(target/n))
    for d in range(0,4000000):
        for s in(1,-1):
            kk=k0+s*d
            if kk<1:continue
            p=kk*n+1
            if p>3 and is_prime(p):
                if odd_m and ((p-1)//n)%2==0:continue
                return p
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
def run():
    print("ODD-r zero-sum count W_r(mu_n) — onset of additive structure (the true Sidon depth).")
    print("W_r=0 => sum_{b!=0} eta_b^r = -n^r EXACTLY (rigid, p-independent).\n")
    for n in [8,16]:
        log2n=int(math.log2(n))
        odd=[r for r in range(3,2*log2n+4,2)]
        print(f"== n={n} (log2={log2n}) ==")
        for beta in [2.4,3.0,4.0,4.6]:
            p=find_prime(int(n**beta),n)
            e=subgroup(n,p)
            rb=math.log(p)/math.log(n)
            cells=[]
            for r in odd:
                w=Wr(e,p,r)
                cells.append(f"r{r}:W={w}")
            first_nz=next((r for r in odd if Wr(e,p,r)>0),None)
            print(f"  beta~{rb:.2f} p={p}: {' '.join(cells)}  | first odd-r W_r>0: {first_nz}")
        print()
if __name__=="__main__":
    run()
