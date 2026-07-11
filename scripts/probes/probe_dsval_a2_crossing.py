#!/usr/bin/env python3
"""
A2 crossing-finder (#407): numpy-accelerated EXACT (big-prime char-0) computation of
worst-direction I_dir(w) and orbit count, to locate delta* and extract the closed form.
Reuses definitions from probe_dsval_a2_orbit_closed_form.py.
"""
import sys, itertools
import numpy as np
from math import gcd

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def find_prime(n,lo,skip=0):
    q=((lo//n)+1)*n+1; found=0
    while True:
        if isprime(q):
            t=q-1; v2=0
            while t%2==0: t//=2; v2+=1
            an=n; v2n=0
            while an%2==0: an//=2; v2n+=1
            if v2<=v2n+2:
                if found==skip: return q
                found+=1
        q+=n

def roots(n,q):
    e=(q-1)//n
    for base in range(2,q):
        c=pow(base,e,q)
        if c==1 or pow(c,n//2,q)==1: continue
        return [pow(c,i,q) for i in range(n)]

INV=None
def build_inv(q):
    global INV
    INV=[0]*q; INV[1]=1
    for i in range(2,q):
        INV[i]=(-(q//i)*INV[q%i])%q

def bad_for_dir(n,k,a,b,w,q,mu):
    """EXACT bad-gamma set for far dir (a,b), agreement w. numpy mod-q linear algebra per subset."""
    bad=set()
    idx=list(range(n))
    for W in itertools.combinations(idx,w):
        # Vandermonde V (w x k), u=x^a, v=x^b over W
        rows=list(W)
        V=np.array([[mu[(i*c)%n] for c in range(k)] for i in rows],dtype=object)
        u=np.array([mu[(i*a)%n] for i in rows],dtype=object)
        v=np.array([mu[(i*b)%n] for i in rows],dtype=object)
        # left null space of V via row-reduction with identity augmentation (python ints mod q)
        wlen=w
        A=[[int(V[r][c])%q for c in range(k)]+[1 if cc==r else 0 for cc in range(wlen)] for r in range(wlen)]
        prow=0
        for col in range(k):
            piv=None
            for r in range(prow,wlen):
                if A[r][col]%q: piv=r; break
            if piv is None: continue
            A[prow],A[piv]=A[piv],A[prow]
            inv=INV[A[prow][col]]
            A[prow]=[(x*inv)%q for x in A[prow]]
            for r in range(wlen):
                if r!=prow and A[r][col]%q:
                    f=A[r][col]; A[r]=[(A[r][cc]-f*A[prow][cc])%q for cc in range(len(A[r]))]
            prow+=1
            if prow==wlen: break
        gc=None; ok=True; anyv=False
        for r in range(prow,wlen):
            if any(A[r][c]%q for c in range(k)): continue
            comb=[A[r][k+j]%q for j in range(wlen)]
            Nu=sum(comb[j]*int(u[j]) for j in range(wlen))%q
            Nv=sum(comb[j]*int(v[j]) for j in range(wlen))%q
            if Nv:
                anyv=True
                gi=(-Nu*INV[Nv])%q
                if gc is None: gc=gi
                elif gi!=gc: ok=False; break
            else:
                if Nu: ok=False; break
        if anyv and ok and gc is not None:
            bad.add(gc)
    return bad

def worst(n,k,w,q,mu,gaps=None):
    best=(-1,None,None,None)
    for a in range(k,n):
        for b in range(a+1,n):
            if gaps is not None and (b-a) not in gaps: continue
            S=n//gcd(b-a,n)
            bad=bad_for_dir(n,k,a,b,w,q,mu)
            I=len(bad)
            # verify orbit closure: bad * mu[b-a] == bad
            mz=mu[(b-a)%n]
            closed=all(((g*mz)%q) in bad for g in bad)
            if I>best[0]: best=(I,(a,b),S,closed)
    return best

if __name__=="__main__":
    n=int(sys.argv[1]); rn=int(sys.argv[2]); rd=int(sys.argv[3])
    wlist=[int(x) for x in sys.argv[4].split(",")]
    gaps=[int(x) for x in sys.argv[5].split(",")] if len(sys.argv)>5 else None
    k=(rn*n)//rd
    q=find_prime(n,n**3+5)
    mu=roots(n,q)
    build_inv(q)
    print(f"# n={n} rho={rn}/{rd} k={k} q={q} budget={n} gaps={gaps}",flush=True)
    for w in wlist:
        I,d,S,closed=worst(n,k,w,q,mu,gaps)
        delta=1-w/n
        norb = (I//S) if (S and I%S==0) else None
        flag="OVER" if I>n else "ok"
        print(f"w={w:2d} delta={delta:.4f}: maxI={I} dir={d} S={S} #orbits={norb} orbit_closed={closed} [{flag} budget {n}]",flush=True)
