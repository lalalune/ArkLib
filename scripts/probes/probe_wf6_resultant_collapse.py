# probe_wf6_resultant_collapse.py (Target A4, Fable 2026-06-13)
#
# Tests the MECHANISM behind conjectures C2 & C3.
#
# For a fixed agreement set T (|T|=a) and stack (u0,u1), the line L(g)=u0+g.u1 is
# explainable on T iff the unique deg<a interpolant P_T(g) of L(g)|_T has degree <k.
# P_T(g) is AFFINE in g (Lagrange), so each of its top (a-k) coefficients (degrees
# k..a-1) is an affine function of g:  coef_j(g) = alpha_j + g.beta_j.
# Explainable-on-T  <=>  alpha_j + g.beta_j = 0  for all j in {k..a-1}.
#   - if some beta_j != 0: at most ONE g works (or none if the alpha/beta ratios
#     disagree across j) -> a UNIQUE candidate bad scalar g_T per T.
#   - if all beta_j = 0 but some alpha_j != 0: NEVER explainable on T.
#   - if all alpha_j=beta_j=0: ALL g (joint regime, T explainable for u0 and u1).
#
# So the bad set is contained in { g_T : T an a-subset with a unique solution }.
# CONJECTURE C2/C3 CLAIM:  for mu_n, the multiset {g_T} COLLAPSES to O(n) distinct
# values (Vieta/cyclotomic resonance), so #bad = O(n), NOT C(n,a) and NOT Theta(q).
#
# We compute, per stack, the DISTINCT g_T values and compare to:
#   - number of a-subsets C(n,a)
#   - n  (the conjectured O(n) collapse)
#   - the actual maxbad (intersect with non-joint condition)
# We compare mu_n domain vs a RANDOM domain vs an AP domain to test domain-dependence.

import itertools, random
from math import comb
from fractions import Fraction

def pf(n):
    f=set();d=2;m=n
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def gen(p,n):
    for a in range(2,p):
        if pow(a,n,p)==1 and all(pow(a,n//q,p)!=1 for q in pf(n)):return a
    return None

def coeffs_of_interp(xs, vals, a, p):
    # deg<a poly interpolant of (xs[i],vals[i]) i in range(a). Return coef list len a.
    A=[[pow(xs[i],j,p) for j in range(a)]+[vals[i]] for i in range(a)]
    for col in range(a):
        piv=next((r for r in range(col,a) if A[r][col]%p),None)
        if piv is None:return None
        A[col],A[piv]=A[piv],A[col];inv=pow(A[col][col],p-2,p)
        A[col]=[(v*inv)%p for v in A[col]]
        for r in range(a):
            if r!=col and A[r][col]%p:
                f=A[r][col];A[r]=[(A[r][t]-f*A[col][t])%p for t in range(a+1)]
    return [A[i][a]%p for i in range(a)]

def g_for_T(T,u0,u1,dom,k,p,a):
    # affine-in-g coefficients of interpolant: coef_j(g)=alpha_j+g*beta_j
    xs=[dom[i] for i in T]
    a0=coeffs_of_interp(xs,[u0[i] for i in T],a,p)  # alpha (g=0)
    if a0 is None:return ('deg',None)
    a1=coeffs_of_interp(xs,[u1[i] for i in T],a,p)   # this is interpolant of u1 = beta directly (linearity)
    if a1 is None:return ('deg',None)
    alpha=a0[k:a];beta=a1[k:a]  # top coeffs of u0-interp, u1-interp
    # need alpha_j + g*beta_j = 0 for all j
    sol=None
    for al,be in zip(alpha,beta):
        if be%p==0:
            if al%p!=0:return ('none',None)  # never
            # 0=0, no constraint
        else:
            cand=(-al*pow(be,p-2,p))%p
            if sol is None:sol=cand
            elif sol!=cand:return ('none',None)  # inconsistent
    if sol is None:return ('all',None)  # joint on T (every g) -> joint, not bad via T
    return ('one',sol)

def analyze(dom,k,p,a,u0,u1):
    n=len(dom)
    gs=[]
    for T in itertools.combinations(range(n),a):
        kind,g=g_for_T(list(T),u0,u1,dom,k,p,a)
        if kind=='one':gs.append(g)
    return gs  # multiset of candidate bad scalars (before non-joint filter)

def run(label,dom,k,p,a,nstacks,seed):
    n=len(dom);random.seed(seed)
    best=(0,None)
    for _ in range(nstacks):
        u0=tuple(random.randrange(p) for _ in range(n))
        u1=tuple(random.randrange(p) for _ in range(n))
        gs=analyze(dom,k,p,a,u0,u1)
        d=len(set(gs))
        if d>best[0]:best=(d,(u0,u1,len(gs)))
    # monomial stacks
    for e0 in range(k,n):
        for e1 in range(k,n):
            u0=tuple(pow(x,e0,p) for x in dom);u1=tuple(pow(x,e1,p) for x in dom)
            gs=analyze(dom,k,p,a,u0,u1);d=len(set(gs))
            if d>best[0]:best=(d,(u0,u1,len(gs)))
    distinct=best[0]
    total = best[1][2] if best[1] else 0
    print(f"  [{label}] a={a}: max DISTINCT candidate-g = {distinct}  "
          f"(raw count {total}, C(n,a)={comb(n,a)}, n={n})  "
          f"=> O(n)? {distinct<=2*n}  collapse_ratio={distinct}/{total if total else 1}")
    return distinct

if __name__=="__main__":
    print("=== resultant/Vieta collapse of candidate bad scalars (C2/C3 mechanism) ===")
    for (p,n,k) in [(41,8,2),(89,8,2),(97,8,2)]:
        g=gen(p,n);mun=[pow(g,j,p) for j in range(n)]
        rnd=random.Random(7).sample(range(1,p),n)
        ap=[(1+5*i)%p for i in range(n)]  # arithmetic progression
        print(f"\n-- p={p} n={n} k={k} --")
        for a in [5,4,3]:
            dm=run("mu_n",mun,k,p,a,120,1)
            dr=run("random",rnd,k,p,a,120,1)
            da=run("AP",ap,k,p,a,120,1)
            print(f"   --> a={a}: mu_n={dm} random={dr} AP={da}  "
                  f"[mu_n COLLAPSES below random? {dm<dr}]")
