#!/usr/bin/env python3
"""
wf407 / T389-02-hill  (v3) -- the DECISIVE, fast experiments.

Three questions, exact answers:

 Q1  Among monomial-PAIR stacks (X^a, X^b) -- the natural far-line objects on mu_n --
     which (a,b) maximizes far-line incidence?  Is it LOW or HIGH exponent? adjacent?
     [reproduce the synthesis deep-band maximizers: (12,6)->(X^9,X^8)=12;
      (16,8) r=8 -> (x^9,x^11)=104 etc.]

 Q2  Does a hill-climb over ARBITRARY (u0,u1) 2-row stacks BEAT the best monomial pair?
     (the thread's "binding family is incomplete" claim).  We hill-climb both rows.

 Q3  Is the far-line incidence operator's extremizer a MONOMIAL direction (the §5.0/R4
     workbench assumption) or genuinely non-monomial?

Far-line incidence for a 2-row stack (u0,u1) at agreement threshold w:
   I = #{gamma : max-agreement(u0+gamma*u1) >= w}.
We compute max-agreement EXACTLY by k-subset interpolation, with a cached Lagrange basis.
For speed we restrict the gamma-sweep smartly and memoize.
"""
import sys, itertools, random, time

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primitive_root(p):
    fs=set(); m=p-1; d=2
    while d*d<=m:
        while m%d==0: fs.add(d);m//=d
        d+=1
    if m>1: fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

class Eng:
    def __init__(self,dom,k,p):
        self.dom=dom;self.k=k;self.p=p;self.n=len(dom)
        self.subs=list(itertools.combinations(range(self.n),k))
        inv=[0]*p
        for a in range(1,p): inv[a]=pow(a,p-2,p)
        self.basis=[]
        for sub in self.subs:
            xs=[dom[j] for j in sub]
            den=[]
            for j in range(k):
                d=1
                for m in range(k):
                    if m!=j: d=(d*(xs[j]-xs[m]))%p
                den.append(inv[d%p])
            rows=[]
            for x in dom:
                cf=[]
                for j in range(k):
                    nu=1
                    for m in range(k):
                        if m!=j: nu=(nu*(x-xs[m]))%p
                    cf.append((nu*den[j])%p)
                rows.append(tuple(cf))
            self.basis.append((sub,rows))
    def max_agree(self,t):
        p=self.p;n=self.n;k=self.k;best=k
        for sub,rows in self.basis:
            tj=[t[j] for j in sub]
            cnt=0
            for i in range(n):
                r=rows[i];v=0
                for jj in range(k): v+=tj[jj]*r[jj]
                if v%p==t[i]: cnt+=1
            if cnt>best:
                best=cnt
                if best==n: return n
        return best
    def incidence(self,u0,u1,w):
        p=self.p;n=self.n;c=0;bad=[]
        for g in range(p):
            t=[(u0[i]+g*u1[i])%p for i in range(n)]
            if self.max_agree(t)>=w: c+=1;bad.append(g)
        return c,bad

def pw(dom,a,p): return [pow(x,a,p) for x in dom]

def q1_q3_monomial_pairs(n,k,p,w,label):
    print(f"\n===== {label}: n={n} k={k} p={p} w={w} (rho={k/n:.3f}) =====",flush=True)
    dom=mu_n(p,n); E=Eng(dom,k,p); mon=[pw(dom,a,p) for a in range(n)]
    best=(None,None,-1); rows=[]
    t0=time.time()
    for a in range(k,n):
        if E.max_agree(mon[a])>=w:  # x^a not far
            continue
        for b in range(0,a):
            c,_=E.incidence(mon[b],mon[a],w)
            rows.append((a,b,c))
            if c>best[2]: best=(a,b,c)
    rows.sort(key=lambda r:-r[2])
    print(" top monomial pairs (X^a,X^b):",flush=True)
    for a,b,c in rows[:8]:
        adj = "ADJ" if a-b==1 else f"gap{a-b}"
        print(f"   (X^{a},X^{b}) I={c}   [{adj}]",flush=True)
    print(f" => BEST monomial pair (X^{best[0]},X^{best[1]}) I={best[2]}   ({time.time()-t0:.1f}s)",flush=True)
    return E,dom,mon,best

def q2_hillclimb_arbitrary(E,dom,mon,n,k,p,w,best_pair,restarts=12,seed=3,label=""):
    """Hill-climb arbitrary 2-row stacks (u0,u1). u1 must stay far (max_agree(u1)<w)."""
    print(f" -- Q2 hill-climb ARBITRARY (u0,u1), {restarts} restarts --",flush=True)
    rng=random.Random(seed)
    def far(u1): return E.max_agree(u1)<w
    def sc(u0,u1):
        if not far(u1): return -1
        return E.incidence(u0,u1,w)[0]
    bestI=-1; bestw=None
    t0=time.time()
    for r in range(restarts):
        # seed from the best monomial pair on half the restarts, random else
        if r%2==0 and best_pair[0] is not None:
            u1=list(mon[best_pair[0]]); u0=list(mon[best_pair[1]])
        else:
            u1=[rng.randrange(p) for _ in range(n)]; u0=[rng.randrange(p) for _ in range(n)]
            # re-roll u1 until far
            tries=0
            while not far(u1) and tries<20:
                u1=[rng.randrange(p) for _ in range(n)]; tries+=1
        cs=sc(u0,u1); imp=True
        while imp:
            imp=False
            # perturb u1 then u0
            for which,vec in ((1,u1),(0,u0)):
                for i in range(n):
                    old=vec[i]; bv,bs=old,cs
                    cand=set(rng.randrange(p) for _ in range(14)) | set(mon[a][i] for a in range(n))
                    for v in cand:
                        if v==old: continue
                        vec[i]=v
                        s=sc(u0,u1)
                        if s>bs: bs,bv=s,v
                    vec[i]=bv
                    if bs>cs: cs=bs; imp=True
        if cs>bestI: bestI=cs; bestw=(list(u0),list(u1))
    print(f"   => hill-climb best far-line incidence I={bestI}  (vs monomial-pair {best_pair[2]})  ({time.time()-t0:.1f}s)",flush=True)
    # classify u1
    u0,u1=bestw
    isMon=False
    for a in range(n):
        m=mon[a];ratios=set();ok=True
        for i in range(n):
            if m[i]==0:
                if u1[i]!=0: ok=False;break
                continue
            ratios.add((u1[i]*pow(m[i],p-2,p))%p)
        if ok and len(ratios)==1:
            print(f"   converged DIRECTION u1 = {ratios}*x^{a} (scaled monomial)",flush=True);isMon=True;break
    if not isMon:
        print(f"   converged DIRECTION u1 is NOT a scaled monomial",flush=True)
    return bestI

if __name__=="__main__":
    # Q1/Q3 + Q2 on (12,6) d=1/4 (fast: C(12,6)=924)
    E,dom,mon,best=q1_q3_monomial_pairs(12,6,13,9,"INST-A (12,6) d=1/4")
    q2_hillclimb_arbitrary(E,dom,mon,12,6,13,9,best,restarts=10,label="A")

    # Q1 deep-band (16,8) w=9: reproduce high-exponent maximizer; monomial-pair scan only (C(16,8)=12870 slower)
    # use smaller witness count to keep speed: w=9
    E2,dom2,mon2,best2=q1_q3_monomial_pairs(16,8,17,9,"INST-B (16,8) w=9")
    q2_hillclimb_arbitrary(E2,dom2,mon2,16,8,17,9,best2,restarts=6,label="B")
