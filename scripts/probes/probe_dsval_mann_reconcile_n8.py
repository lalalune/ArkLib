#!/usr/bin/env python3
"""
probe_dsval_mann_reconcile_n8.py  (#407 A5 -- reconcile brute vs Mann-coset for n=8)

FINDING TO EXPLAIN: brute-force I(w=5) = 8 distinct gammas (dir (4,5)) but the
Mann-coset-union enumeration found only I=2.  So either (a) the budget-relevant
agreement sets are NOT pure cyclotomic-coset unions, or (b) there are multiple
gammas per coset-union via different DIRECTIONS, or (c) the brute count over-counts.

This probe, EXACTLY over p>>n^4, for n=8, dir (4,5), k=2:
  * enumerate ALL gammas reachable (from (k+1)-subset consistency), and for each list
    its FULL agreement set S (the max-agreement codeword's agreement set), then
    classify S: is it a union of cyclotomic cosets? what's its antipodal structure?
  * print the actual S for the 8 gammas at w>=5.
This tells us the TRUE combinatorial object governing I(delta) -> closed form.
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
def v2(x):
    if x==0:return 99
    c=0
    while x%2==0:x//=2;c+=1
    return c

def max_agreement_set(mu,a,b,gamma,k,p,n):
    idxs=list(range(n))
    h=[(pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p for i in idxs]
    best=0;bs=None
    for anchor in itertools.combinations(idxs,k):
        xs=[mu[i] for i in anchor];ys=[h[i] for i in anchor]
        agr=[]
        for i in idxs:
            tot=0;x=mu[i]
            for t in range(k):
                num=ys[t];den=1
                for s in range(k):
                    if s==t:continue
                    num=num*((x-xs[s])%p)%p;den=den*((xs[t]-xs[s])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            if tot==h[i]:agr.append(i)
        if len(agr)>best:best=len(agr);bs=set(agr)
    return bs

def is_coset_union(S,n):
    a=int(round(log2(n)))
    cos=[[0]]+[[i for i in range(1,n) if v2(i)==a-j] for j in range(1,a+1)]
    cells=[set(c) for c in cos]
    rem=set(S)
    used=[]
    for idx,c in enumerate(cells):
        if c<=rem:
            rem-=c;used.append(idx)
    return (len(rem)==0, used)

def main():
    n=8;p=find_prime(n,n**4*4)
    mu=rou(p,n)
    for k in [2,4]:
        print(f"\n===== n={n} k={k} p={p} =====")
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
        # find dir with max I at the boundary; reproduce brute
        for (a,b) in dirs:
            gset=set()
            for T in itertools.combinations(range(n),k+1):
                xs=[mu[i] for i in T]
                c=[]
                for i in range(k+1):
                    den=1
                    for j in range(k+1):
                        if j==i:continue
                        den=den*((xs[i]-xs[j])%p)%p
                    c.append(pow(den,p-2,p))
                La=sum(c[i]*pow(xs[i],a,p) for i in range(k+1))%p
                Lb=sum(c[i]*pow(xs[i],b,p) for i in range(k+1))%p
                if Lb==0:continue
                gset.add((-La*pow(Lb,p-2,p))%p)
            entries=[]
            for g in gset:
                S=max_agreement_set(mu,a,b,g,k,p,n)
                entries.append((g,S))
            # boundary w for this dir
            wcount={}
            for w in range(k+1,n+1):
                wcount[w]=sum(1 for g,S in entries if len(S)>=w)
            # only print directions that are interesting (reach high w)
            maxw=max((len(S) for g,S in entries),default=0)
            if maxw>=k+2:
                print(f" dir({a},{b}): maxw={maxw}  I-by-w={[(w,wcount[w]) for w in range(k+1,n+1) if wcount[w]>0]}")
                for g,S in sorted(entries,key=lambda e:-len(e[1]))[:6]:
                    if len(S)>=k+1:
                        ok,used=is_coset_union(S,n)
                        Sl=sorted(S)
                        anti=sorted(set((min(i,(i+n//2)%n)) for i in Sl))
                        pairfull=all(((i+n//2)%n) in S for i in Sl)
                        print(f"    g={g:6d} |S|={len(S)} S={Sl} cosetUnion={ok} antipodal_closed={pairfull}")

if __name__=="__main__":
    main()
