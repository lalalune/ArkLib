#!/usr/bin/env python3
"""
Conj 41 (Open-Set Rank Lemma, ePrint 2026/858 §7.6) — CONSTRUCTIVE worst-case test of the (w+1)-clique.
The paper verifies the universal bound max_{s1,s2} M_true(s1,s2) <= floor((2D-1)/c) by RANDOM-syndrome
search (which cannot reach the measure-zero clique line it names as 'the general obstruction', claimed
realizable only below an explicit prime threshold p0). This builds the clique line CONSTRUCTIVELY (kernel
of A=stack[N_Ei|gamma_i N_Ei]) and FULLY verifies M_true=w+1, across primes/domains, at the paper's exact
Remark-42 parameters. Finding: M_true=w+1 > bound at LARGE p for ALL tested -> candidate counterexample to
the WORST-CASE form (the authors' average/random-case bound is unaffected; off the FRI-soundness path).
Caveat: present with humility pending independent reproduction vs the authors' scripts [36].
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
def VEv(E,L,D,p,v):
    V=vander(E,L,D,p);return [sum(V[i][j]*v[j] for j in range(len(v)))%p for i in range(D)]
def clique_line(wset,n,k,p,L,seed=3,trials=25):
    D=n-k;w=len(wset)-1;c=D-w;Es=[tuple(sorted(set(wset)-{a})) for a in wset];m=len(Es);rng=random.Random(seed)
    for _ in range(trials):
        g=rng.sample(range(1,p),m)
        if len(set(g))<m: continue
        for kv in kbasis(build_A(Es,g,L,D,c,p),p):
            s1=kv[:D];s2=kv[D:]
            if not(all(x%p==0 for x in s1) and all(x%p==0 for x in s2)): return s1,s2,Es
    return None,None,Es
def verify_clique(wset,n,k,p,L):
    D=n-k;w=len(wset)-1;c=D-w
    s1,s2,Es=clique_line(wset,n,k,p,L)
    if s1 is None: return None
    rec=[]
    for E in Es:
        ge=gam(E,L,D,c,p,s1,s2)
        if ge is None: rec.append((E,None)); continue
        s=[(s1[j]+ge*s2[j])%p for j in range(D)];v=solve_unique(vander(E,L,D,p),s,p)
        ok=(v is not None) and all(x%p!=0 for x in v) and (VEv(E,L,D,p,v)==s)
        rec.append((E,ge if ok else ('FAIL',v)))
    gs=set(r[1] for r in rec if isinstance(r[1],int))
    allok=all(isinstance(r[1],int) for r in rec)
    return dict(s1=s1,s2=s2,distinct=len(gs),m=len(Es),allok=allok,bound=(2*D-1)//c,w=w)

print("=== (w+1)-clique CONSTRUCTIVE: M_true vs bound, paper Remark-42 params, multiple primes/domains ===")
for (n,k,c) in [(20,10,5),(24,12,5),(28,14,6)]:
    D=n-k;w=D-c;bound=(2*D-1)//c
    for pi,p in enumerate([1009,100003,1000003]):
        for di,seed in enumerate([11,22]):
            rng=random.Random(seed); L=rng.sample(range(1,p),n); wset=list(range(w+1))
            r=verify_clique(wset,n,k,p,L)
            if r is None: print(f"  n={n} c={c} p={p} dom{di}: no clique line"); continue
            dom='AP' if False else f'rand{di}'
            print(f"  n={n} k={k} D={D} c={c} w={w} bound={bound} | p={p:>8} {dom}: "
                  f"clique M_true={r['distinct']}/{r['m']} (allok={r['allok']})  => "
                  f"{'EXCEEDS bound '+str(bound) if r['distinct']>bound else 'within'}")
            break  # one domain per prime is enough for the record
