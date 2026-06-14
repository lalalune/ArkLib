#!/usr/bin/env python3
"""Calibration: for the canonical mu_s Kambire stack (b-a=n/s) compute exact bad-scalar count at each
agreement tau, and compare to the closed form |H^{(+r)}(mu_s)| to extract r(tau,s). Resolves whether
bad-count = |H^{(+r)}| and with what (s,r,delta) map."""
import itertools, math

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def find_q(n,beta):
    base=n**beta; m=base+((1-base)%n)
    while not((m-1)%n==0 and is_prime(m)): m+=n
    return m
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def inv(a,q):
    a%=q; g,x,_=egcd(a,q); return x%q
def subgroup(n,q):
    for c in range(2,q):
        h=pow(c,(q-1)//n,q)
        if pow(h,n,q)!=1: continue
        if n>1 and pow(h,n//2,q)==1: continue
        return [pow(h,i,q) for i in range(n)]
def matinv(M,q):
    t=len(M); A=[row[:]+[1 if i==j else 0 for j in range(t)] for i,row in enumerate(M)]
    for c in range(t):
        piv=next((r for r in range(c,t) if A[r][c]%q),None)
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]; ip=inv(A[c][c],q); A[c]=[(x*ip)%q for x in A[c]]
        for r in range(t):
            if r!=c and A[r][c]%q:
                f=A[r][c]; A[r]=[(A[r][j]-f*A[c][j])%q for j in range(2*t)]
    return [row[t:] for row in A]
def L1count(D,r):
    a=[0]*(r+1); a[0]=1
    for _ in range(D):
        b=[0]*(r+1)
        for t in range(r+1):
            if a[t]==0: continue
            for u in range(0,r-t+1): b[t+u]+=a[t]*(1 if u==0 else 2)
        a=b
    return sum(a[t] for t in range(r+1) if t%2==r%2)

def stack_badcount_at_tau(n,q,k,a,b,tau,elts,XS):
    bad=set()
    for Sidx in itertools.combinations(range(n),tau):
        S=[elts[i] for i in Sidx]
        V=[[pow(x,j,q) for j in range(tau)] for x in S]; Vi=matinv(V,q)
        if Vi is None: continue
        W=Vi[k:tau]
        ok=True; al=None
        for r in range(tau-k):
            pj=sum(W[r][i]*XS[Sidx[i]][a] for i in range(tau))%q
            qj=sum(W[r][i]*XS[Sidx[i]][b] for i in range(tau))%q
            if qj%q==0:
                if pj%q: ok=False; break
            else:
                v=(-pj*inv(qj,q))%q
                if al is None: al=v
                elif al!=v: ok=False; break
        if ok and al is not None and al%q!=0: bad.add(al)
    return len(bad)

def run(n,rn,rd,beta):
    q=find_q(n,beta); elts=subgroup(n,q); k=max(1,(n*rn)//rd)
    XS=[[pow(x,a,q) for a in range(n)] for x in elts]
    print(f"\n=== n={n} q={q} rho={rn}/{rd} k={k} : single-stack bad-count vs |H^(+r)(mu_s)| ===",flush=True)
    for s in [d for d in (n,n//2,n//4) if d>=2]:
        m=n//s                      # b-a = n/s gives orbit subgroup size s
        b=n-1; a=n-1-m              # FAR stack: a,b >= k, b-a=m=n/s (orbit subgroup mu_s)
        if a<k: continue
        D=s//2
        print(f" -- stack (a={a},b={b}), b-a={m}, orbit subgroup s={s}:",flush=True)
        for tau in range(k+1,n):
            bc=stack_badcount_at_tau(n,q,k,a,b,tau,elts,XS)
            # compare to |H^(+r)(mu_s)| for r=tau-k and r=n-tau
            r1=tau-k; r2=n-tau
            h1=L1count(D,r1) if r1>=0 else 0
            h2=L1count(D,r2) if r2>=0 else 0
            print(f"      tau={tau} (d={1-tau/n:.3f}): badcount={bc:5d}   |H^(+{r1})|={h1:6d}  |H^(+{r2})|={h2:6d}",flush=True)

run(16,1,2,3)
run(16,1,4,3)
