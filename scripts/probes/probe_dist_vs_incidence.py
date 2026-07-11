#!/usr/bin/env python3
"""
Does the WORST-incidence far direction MINIMIZE coset distance? (claim D of TowerSupplySubAverage)
Sweep many far directions, record (coset_min_weight, incidence), see correlation.
n=8 q=257 k=4 window-interior w=3 (d=0.375 above J=0.293).
"""
import itertools, random
def rou(q,n):
    for g in range(2,q):
        x=1;s=set()
        for _ in range(q-1): x=x*g%q;s.add(x)
        if len(s)==q-1: o=pow(g,(q-1)//n,q);return [pow(o,i,q) for i in range(n)]
def maxagree(mu,vals,q,k,n,inv):
    best=0
    for sub in itertools.combinations(range(n),k):
        c=0
        for t in range(n):
            xt=mu[t];acc=0
            for j in range(k):
                num=1;den=1
                for l in range(k):
                    if l!=j: num=num*(xt-mu[sub[l]])%q; den=den*(mu[sub[j]]-mu[sub[l]])%q
                acc=(acc+vals[sub[j]]*num*inv[den%q])%q
            if acc==vals[t]: c+=1
        if c>best: best=c
    return best
def nbad(mu,u0,u1,q,k,n,a,inv):
    c=0
    for g in range(q):
        v=[(u0[i]+g*u1[i])%q for i in range(n)]
        if maxagree(mu,v,q,k,n,inv)>=a: c+=1
    return c
q,n,k,w=257,8,4,3
inv=[0]*q
for x in range(1,q): inv[x]=pow(x,q-2,q)
mu=rou(q,n); a=n-w; rng=random.Random(11)
mon=[[pow(mu[i],e,q) for i in range(n)] for e in range(n)]
# For each far direction, max incidence over a few offsets, record (cosetweight, incidence).
buckets={}  # cosetweight -> max incidence seen
def consider(u1):
    ag=maxagree(mu,u1,q,k,n,inv)
    if ag>=a: return  # not far
    cw=n-ag
    I=0
    for _ in range(25):
        u0=[rng.randrange(q) for _ in range(n)]
        I=max(I,nbad(mu,u0,u1,q,k,n,a,inv))
    for b in range(min(n,8)):
        I=max(I,nbad(mu,mon[b],u1,q,k,n,a,inv))
    if cw not in buckets or I>buckets[cw]: buckets[cw]=I
# sweep: monomials, random, codeword+spike
for e in range(n): consider(mon[e])
for _ in range(60): consider([rng.randrange(q) for _ in range(n)])
print(f"n={n} q={q} k={k} w={w} d={w/n:.3f} a={a}  (MDS dist=n-k={n-k})")
print("coset_min_weight -> max incidence found (does MIN distance -> MAX incidence?):")
for cw in sorted(buckets): print(f"   coset-wt {cw}: max I = {buckets[cw]}")
print("done")
