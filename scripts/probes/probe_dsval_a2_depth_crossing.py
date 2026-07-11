#!/usr/bin/env python3
"""
A2 (#407): worst far-direction bad count I vs over-determination depth t = w - k.
EXACT char-0 (big prime, p-independent over-det band). Locates delta* = 1 - (k+t*)/n,
t* = min depth with max_dir I_dir <= budget n. Also reports the Lam-Leung coset-prediction
|H^{+r}(mu_s)| for the worst direction (s=n/gcd(gap,n), r=w/gcd) and orbit count I/s.
"""
import sys, itertools
from math import gcd, comb

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def find_prime(n,lo):
    q=((lo//n)+1)*n+1
    while True:
        if isprime(q):
            t=q-1; v2=0
            while t%2==0: t//=2; v2+=1
            an=n; v2n=0
            while an%2==0: an//=2; v2n+=1
            if v2<=v2n+2: return q
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
    for i in range(2,q): INV[i]=(-(q//i)*INV[q%i])%q

def bad_for_dir(n,k,a,b,w,q,mu):
    bad=set()
    for W in itertools.combinations(range(n),w):
        rows=list(W); wlen=w
        A=[[mu[(i*c)%n] for c in range(k)]+[1 if cc==r else 0 for cc in range(wlen)] for r,i in enumerate(rows)]
        prow=0
        for col in range(k):
            piv=None
            for r in range(prow,wlen):
                if A[r][col]%q: piv=r; break
            if piv is None: continue
            A[prow],A[piv]=A[piv],A[prow]
            inv=INV[A[prow][col]]; A[prow]=[(x*inv)%q for x in A[prow]]
            for r in range(wlen):
                if r!=prow and A[r][col]%q:
                    f=A[r][col]; A[r]=[(A[r][cc]-f*A[prow][cc])%q for cc in range(len(A[r]))]
            prow+=1
            if prow==wlen: break
        u=[mu[(i*a)%n] for i in rows]; v=[mu[(i*b)%n] for i in rows]
        gc=None; ok=True; anyv=False
        for r in range(prow,wlen):
            if any(A[r][c]%q for c in range(k)): continue
            comb_=[A[r][k+j]%q for j in range(wlen)]
            Nu=sum(comb_[j]*u[j] for j in range(wlen))%q
            Nv=sum(comb_[j]*v[j] for j in range(wlen))%q
            if Nv:
                anyv=True; gi=(-Nu*INV[Nv])%q
                if gc is None: gc=gi
                elif gi!=gc: ok=False; break
            else:
                if Nu: ok=False; break
        if anyv and ok and gc is not None: bad.add(gc)
    return bad

if __name__=="__main__":
    n=int(sys.argv[1]); rn=int(sys.argv[2]); rd=int(sys.argv[3])
    k=(rn*n)//rd
    q=find_prime(n,n**3+5); build_inv(q); mu=roots(n,q)
    print(f"# n={n} rho={rn}/{rd} k={k} q={q} budget={n}",flush=True)
    print(f"# t=w-k  delta=1-w/n  maxI  worst_dir(gap)  Hr_coset_pred  orbit=I/S  flag",flush=True)
    prev_ok=None; tstar=None
    # scan from large w (small delta, shallow depth) downward to find crossing
    for w in range(n-1, k, -1):
        t=w-k; delta=1-w/n
        best=(-1,None,None,None)
        for a in range(k,n):
            for b in range(a+1,n):
                bad=bad_for_dir(n,k,a,b,w,q,mu)
                I=len(bad)
                if I>best[0]:
                    d=b-a; dp=gcd(d,n); s=n//dp; r=w//dp if w%dp==0 else None
                    best=(I,(a,b),dp,(s,r))
        I,d,gp,(s,r)=best
        Hr = None
        flag="ok" if I<=n else "OVER"
        S=n//gp
        orb = (I//S) if I%S==0 else None
        print(f"t={t} delta={delta:.4f}: maxI={I} dir={d} gap={d[1]-d[0]} d'={gp} (s={s},r={r}) S={S} orbit={orb} [{flag}]",flush=True)
        if I>n and prev_ok:  # crossing: this depth over, shallower was ok
            tstar=t+1
        prev_ok = (I<=n)
    print(f"# => t* (min depth with I<=n) gives delta* = 1-(k+t*)/n",flush=True)
