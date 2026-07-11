#!/usr/bin/env python3
"""
Toward the GRAND LIST-DECODING challenge: pin the TRUE worst-case M_true(s1,s2) law for the FRI
codimension regime, given Conj 41's bound floor((2D-1)/c) is refuted by the (w+1)-clique (M_true=w+1).
Question: do larger "fat-clique" (w+t)-sets push max M_true above w+1?
For a point-set T (|T|=w+t), take ALL its size-w subsets as supports, build the stacked constraint
matrix A=[N_E|gamma_E N_E], find a common-line kernel, and count GENUINE distinct-gamma nonzero-error
decodings on that line (over ALL supports, not just T's). Report max M_true vs w+1 and vs the (refuted)
floor((2D-1)/c).
"""
import itertools, random, functools
print=functools.partial(print,flush=True)
exec(open('scripts/probes/probe_conj41_kernel.py').read().split('print("=== Conj41')[0])
def kbasis(M,p):
    R=len(M);C=len(M[0]);A=[r[:] for r in M];wh=[-1]*C;pr=0
    for c in range(C):
        pv=next((i for i in range(pr,R) if A[i][c]%p!=0),None)
        if pv is None: continue
        A[pr],A[pv]=A[pv],A[pr];iv=pow(A[pr][c]%p,p-2,p);A[pr]=[(x*iv)%p for x in A[pr]]
        for i in range(R):
            if i!=pr and A[i][c]%p!=0:
                f=A[i][c]%p;A[i]=[(A[i][j]-f*A[pr][j])%p for j in range(C)]
        wh[c]=pr;pr+=1
    pivs=[c for c in range(C) if wh[c]!=-1];fr=[c for c in range(C) if wh[c]==-1];B=[]
    for fc in fr:
        v=[0]*C;v[fc]=1
        for c in pivs: v[c]=(-A[wh[c]][fc])%p
        B.append(v)
    return B
def gam(E,L,D,c,p,s1,s2):
    N=normals(E,L,D,c,p);a=[sum(N[i][j]*s1[j] for j in range(D))%p for i in range(c)]
    b=[sum(N[i][j]*s2[j] for j in range(D))%p for i in range(c)];g=None
    for i in range(c):
        if b[i]%p==0:
            if a[i]%p!=0: return None
        else:
            gi=(-a[i]*pow(b[i],p-2,p))%p
            if g is None: g=gi
            elif g!=gi: return None
    return g
def Mtrue_on_line(s1,s2,n,w,D,c,p,L,subs):
    good=set()
    for E in subs:
        ge=gam(E,L,D,c,p,s1,s2)
        if ge is None: continue
        s=[(s1[j]+ge*s2[j])%p for j in range(D)];v=solve_unique(vander(E,L,D,p),s,p)
        if v is not None and all(x%p!=0 for x in v): good.add(ge)
    return len(good)
def fatclique_best(n,k,c,t,p,L,seed=1,gtrials=8):
    """T = first (w+t) points; supports = ALL size-w subsets of T. Find best common line, return max M_true."""
    D=n-k;w=D-c; T=list(range(w+t)); Es=list(itertools.combinations(T,w)); m=len(Es)
    rng=random.Random(seed); subs=list(itertools.combinations(range(n),w)); best=0
    for _ in range(gtrials):
        gs=[rng.randrange(1,p) for _ in range(m)]
        if len(set(gs))<m: continue
        A=build_A(Es,gs,L,D,c,p)
        for kv in kbasis(A,p):
            s1=kv[:D];s2=kv[D:]
            if all(x%p==0 for x in s1) and all(x%p==0 for x in s2): continue
            best=max(best, Mtrue_on_line(s1,s2,n,w,D,c,p,L,subs))
    return best, w+1, (2*D-1)//c, len(Es)

print("=== TRUE worst-case M_true: fat-clique (w+t)-sets, FRI regime, large p ===")
for (n,k,c) in [(20,10,5),(24,12,5)]:
    D=n-k;w=D-c;p=1000003; rng=random.Random(9); L=rng.sample(range(1,p),n)
    print(f"\n n={n} k={k} D={D} c={c} w={w} | (refuted) floor((2D-1)/c)={(2*D-1)//c} | single-clique gives w+1={w+1}")
    for t in [1,2,3]:
        if w+t>n: continue
        best,wp1,bnd,nsup=fatclique_best(n,k,c,t,p,L,gtrials=6)
        print(f"   (w+{t})-set [{w+t} pts, {nsup} size-{w} supports]: max M_true on a common line = {best}  (vs w+1={wp1})")
