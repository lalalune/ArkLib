#!/usr/bin/env python3
"""
wf407 / T389-02-hill : Q2 -- does a hill-climb over ARBITRARY (u0,u1) 2-row stacks BEAT the
best MONOMIAL pair?  (the thread's 'binding family is incomplete' claim, for the far-line
incidence object I(delta) -- NOT the max-list object O163 already settled.)

Instance: (12,6) d=1/4, p=13, w=9.  Best monomial pair = (X^9,X^8), I=12.
We hill-climb both rows of a 2-row stack to convergence with many restarts and strong moves.
Fast exact engine (cached Lagrange basis), foreground-friendly.
"""
import itertools, random, time
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def primitive_root(p):
    fs=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fs.add(d);m//=d
        d+=1
    if m>1:fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def mu_n(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]
class Eng:
    def __init__(self,dom,k,p):
        self.dom=dom;self.k=k;self.p=p;self.n=len(dom)
        inv=[0]*p
        for a in range(1,p):inv[a]=pow(a,p-2,p)
        self.basis=[]
        for sub in itertools.combinations(range(self.n),k):
            xs=[dom[j] for j in sub];den=[]
            for j in range(k):
                d=1
                for m in range(k):
                    if m!=j:d=(d*(xs[j]-xs[m]))%p
                den.append(inv[d%p])
            rows=[]
            for x in dom:
                cf=[]
                for j in range(k):
                    nu=1
                    for m in range(k):
                        if m!=j:nu=(nu*(x-xs[m]))%p
                    cf.append((nu*den[j])%p)
                rows.append(tuple(cf))
            self.basis.append((sub,rows))
    def max_agree(self,t):
        p=self.p;n=self.n;k=self.k;best=k
        for sub,rows in self.basis:
            tj=[t[j] for j in sub];cnt=0
            for i in range(n):
                r=rows[i];v=0
                for jj in range(k):v+=tj[jj]*r[jj]
                if v%p==t[i]:cnt+=1
            if cnt>best:
                best=cnt
                if best==n:return n
        return best
    def incidence(self,u0,u1,w):
        p=self.p;n=self.n;c=0
        for g in range(p):
            t=[(u0[i]+g*u1[i])%p for i in range(n)]
            if self.max_agree(t)>=w:c+=1
        return c

def run(n,k,p,w,restarts,seed=11):
    dom=mu_n(p,n);E=Eng(dom,k,p);mon=[[pow(x,a,p) for x in dom] for a in range(n)]
    rng=random.Random(seed)
    def far(u1):return E.max_agree(u1)<w
    def sc(u0,u1):
        if not far(u1):return -1
        return E.incidence(u0,u1,w)
    monpair=(9,8); base=E.incidence(mon[8],mon[9],w)
    print(f"(12,6) baseline: monomial pair (X^9,X^8) I={base}",flush=True)
    bestI=-1;bestw=None;t0=time.time()
    for r in range(restarts):
        if r==0: u0,u1=list(mon[8]),list(mon[9])         # seed from extremal monomial pair
        elif r%3==1:
            a=rng.randrange(k,n);b=rng.randrange(0,a);u0,u1=list(mon[b]),list(mon[a])
        else:
            u1=[rng.randrange(p) for _ in range(n)]
            t=0
            while not far(u1) and t<30:u1=[rng.randrange(p) for _ in range(n)];t+=1
            u0=[rng.randrange(p) for _ in range(n)]
        cs=sc(u0,u1);imp=True
        while imp:
            imp=False
            for vec in (u1,u0):
                for i in range(n):
                    old=vec[i];bv,bs=old,cs
                    for v in range(p):
                        if v==old:continue
                        vec[i]=v;s=sc(u0,u1)
                        if s>bs:bs,bv=s,v
                    vec[i]=bv
                    if bs>cs:cs=bs;imp=True
        if cs>bestI:bestI=cs;bestw=(list(u0),list(u1))
    print(f"hill-climb best far-line incidence I={bestI}  (monomial-pair baseline {base})  ({time.time()-t0:.1f}s, {restarts} restarts, FULL-field moves)",flush=True)
    u0,u1=bestw
    isMon=False
    for a in range(n):
        m=mon[a];ratios=set();ok=True
        for i in range(n):
            if m[i]==0:
                if u1[i]!=0:ok=False;break
                continue
            ratios.add((u1[i]*pow(m[i],p-2,p))%p)
        if ok and len(ratios)==1:
            print(f"  best DIRECTION u1 = {ratios}*x^{a} (scaled monomial, exp {a})",flush=True);isMon=True;break
    if not isMon: print("  best DIRECTION u1 is NOT a scaled monomial",flush=True)
    print(f"  verdict: arbitrary {'BEATS' if bestI>base else 'does NOT beat'} monomial-pair "
          f"({bestI} vs {base})",flush=True)

if __name__=="__main__":
    run(12,6,13,9,restarts=8)
