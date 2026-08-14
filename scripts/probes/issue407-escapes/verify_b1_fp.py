import numpy as np
from sympy import primerange, factorint
from itertools import combinations

def find_prime(n):
    for p in primerange(3, 200000):
        if (p-1)%n==0: return p
    return None

def sympy_factors(n):
    return list(factorint(n).keys())

def prim_root_subgroup(p,n):
    g=2
    while True:
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in sympy_factors(n)):
            return h
        g+=1

def coset_core(idxset, n):
    S=set(idxset); best=set()
    for g in range(2,n+1):
        if n%g: continue
        step=n//g; seen=set(); cosets=[]
        for j in range(n):
            if j in seen: continue
            cs=set((j+step*t)%n for t in range(g)); seen|=cs; cosets.append(cs)
        core=set()
        for cs in cosets:
            if cs<=S: core|=cs
        if len(core)>len(best): best=core
    return best

def solve_modp(M,rhs,p):
    n=len(M)
    A=[row[:]+[rhs[i]] for i,row in enumerate(M)]
    for col in range(n):
        piv=None
        for r in range(col,n):
            if A[r][col]%p!=0: piv=r;break
        if piv is None: return None
        A[col],A[piv]=A[piv],A[col]
        inv=pow(A[col][col],p-2,p)
        A[col]=[(x*inv)%p for x in A[col]]
        for r in range(n):
            if r!=col and A[r][col]%p!=0:
                f=A[r][col]; A[r]=[(A[r][j]-f*A[col][j])%p for j in range(n+1)]
    return [A[i][n]%p for i in range(n)]

for n in [8,16,32]:
    p=find_prime(n); h=prim_root_subgroup(p,n)
    mu=[pow(h,i,p) for i in range(n)]
    for k in [2,3]:
        bestexcess=0; rec=None; nonvanish_seen=False; antip_all=True; any_excess=False
        for a in range(1,n):
            for b in range(0,a):
                if np.gcd(a-b,n)<2: continue
                if a==n//2 or b==n//2: continue
                glim=min(p-1,150)
                for gamma in range(1,glim+1):
                    F=[(pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p for i in range(n)]
                    for T in combinations(range(n),k):
                        M=[[pow(mu[t],j,p) for j in range(k)] for t in T]
                        rhs=[F[t] for t in T]
                        sol=solve_modp(M,rhs,p)
                        if sol is None: continue
                        cvals=[sum(sol[j]*pow(mu[i],j,p) for j in range(k))%p for i in range(n)]
                        S=[i for i in range(n) if F[i]==cvals[i]]
                        if len(S)<=k+1: continue
                        core=coset_core(S,n)
                        if len(core)>=len(S): continue
                        any_excess=True
                        R=sorted(set(S)-core)
                        ssum=sum(mu[i] for i in R)%p
                        if ssum!=0: nonvanish_seen=True
                        antip=len(R)>0 and all(((i+n//2)%n) in set(R) for i in R)
                        if not antip: antip_all=False
                        excess=len(S)-len(core)
                        if excess>bestexcess:
                            bestexcess=excess; rec=(a,b,gamma,len(S),len(core),R,ssum,antip)
        print(f"n={n} p={p} k={k} sqrt(nk)={(n*k)**0.5:.2f} 2k-1={2*k-1}: maxexcess={bestexcess} nonvanishingFound={nonvanish_seen} allAntipodal={antip_all if any_excess else 'NA'} rec={rec}")
