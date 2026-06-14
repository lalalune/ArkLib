#!/usr/bin/env python3
"""General q-stability probe for the far-line incidence I(delta).
Usage: qstab_general.py N K TAU PMIN PMAX [MAXPRIMES]
Computes total I(delta) = sum over far stacks (a,b>=k, a<b<n) of #{bad scalars} at agreement TAU,
over primes q = 1 mod N in (PMIN, PMAX]. Prints q, I, and whether I is constant. Reports the
stabilization: the value for q > (2k)^4 and whether all such agree."""
import itertools, sys
def isp(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True
def egcd(a,b):
    if b==0:return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,q):
    a%=q;g,x,_=egcd(a,q);return x%q
def subgroup(n,q):
    for c in range(2,q):
        h=pow(c,(q-1)//n,q)
        if pow(h,n,q)!=1:continue
        if n>1 and pow(h,n//2,q)==1:continue
        return [pow(h,i,q) for i in range(n)]
def matinv(M,q):
    t=len(M);A=[r[:]+[1 if i==j else 0 for j in range(t)] for i,r in enumerate(M)]
    for c in range(t):
        piv=next((r for r in range(c,t) if A[r][c]%q),None)
        if piv is None:return None
        A[c],A[piv]=A[piv],A[c];ip=inv(A[c][c],q);A[c]=[(x*ip)%q for x in A[c]]
        for r in range(t):
            if r!=c and A[r][c]%q:
                f=A[r][c];A[r]=[(A[r][j]-f*A[c][j])%q for j in range(2*t)]
    return [r[t:] for r in A]
def total_I(n,q,k,tau,elts):
    XS=[[pow(x,aa,q) for aa in range(n)] for x in elts]
    tot=0
    for a in range(k,n):
        for b in range(a+1,n):
            bad=set()
            for Sidx in itertools.combinations(range(n),tau):
                S=[elts[i] for i in Sidx]
                V=[[pow(x,j,q) for j in range(tau)] for x in S];Vi=matinv(V,q)
                if Vi is None:continue
                ok=True;al=None
                for r in range(tau-k):
                    pj=sum(Vi[k+r][i]*XS[Sidx[i]][a] for i in range(tau))%q
                    qj=sum(Vi[k+r][i]*XS[Sidx[i]][b] for i in range(tau))%q
                    if qj%q==0:
                        if pj%q:ok=False;break
                    else:
                        v=(-pj*inv(qj,q))%q
                        if al is None:al=v
                        elif al!=v:ok=False;break
                if ok and al is not None and al%q!=0:bad.add(al)
            tot+=len(bad)
    return tot
def main():
    n=int(sys.argv[1]);k=int(sys.argv[2]);tau=int(sys.argv[3])
    pmin=int(sys.argv[4]);pmax=int(sys.argv[5])
    maxp=int(sys.argv[6]) if len(sys.argv)>6 else 999
    thr=(2*k)**4
    print(f"# n={n} k={k} tau={tau} delta={1-tau/n:.4f}  (2k)^4={thr}",flush=True)
    vals_above={}; vals_below={}; cnt=0; q=max(pmin,n+1)
    while q<=pmax and cnt<maxp:
        if isp(q) and (q-1)%n==0:
            e=subgroup(n,q)
            if e is not None:
                I=total_I(n,q,k,tau,e); cnt+=1
                tag="ABOVE" if q>thr else "below"
                print(f"q={q} I={I} {tag}",flush=True)
                (vals_above if q>thr else vals_below)[q]=I
        q+=1
    av=sorted(set(vals_above.values()))
    print(f"# RESULT: distinct I-values for q>(2k)^4: {av}  -> {'STABLE' if len(av)<=1 else 'UNSTABLE'}",flush=True)
    print(f"# below-(2k)^4 distinct values: {sorted(set(vals_below.values()))}",flush=True)
if __name__=="__main__": main()
