#!/usr/bin/env python3
"""
UNDER-DET lane (#444), PART 3 — the AGREEMENT-SET PACKING structure that bounds #pinnedScalars.

Established (in-tree): #bad = #pinnedScalars (BadScalarsEqPinned), census = Sum_g C(|A_g|, a)
(AgreementSetMaximal + CensusScalarPartition), and distinct g <-> non-degenerate aligned sets are
disjoint at the SET level (alignedSetsForScalar_disjoint). OPEN: a bound on #pinnedScalars itself.

THE PACKING LEVER (this probe): the agreement sets {A_g : g pinned} are the maximal g-aligned sets.
CLAIM: two distinct pinned scalars g != g' have agreement sets overlapping in AT MOST k points.
  Reason: if |A_g ∩ A_g'| >= k+1, pick a (k+1)-tuple T inside the intersection. T is g-aligned AND
  g'-aligned. By Aligned.gamma_eq, IF T is non-degenerate (residual u0,u1 not both 0 on T) then
  g = g', contradiction. So every (k+1)-tuple in A_g ∩ A_g' is DEGENERATE (jointly deg<k). If the
  whole intersection is jointly-deg<k it can still be large -- BUT then it is a JOINT-AGREEMENT set
  (pairJointAgreesOn), the degenerate object the census excludes. So either:
    (a) |A_g ∩ A_g'| <= k  (genuine bounded overlap, Fisher/sunflower packing), OR
    (b) A_g ∩ A_g' is jointly-deg<k (a single shared degenerate core, same for ALL pairs).

If (a) dominates: the {A_g} are a near-packing => Sum |A_g| <= n + (overlaps) => with each
|A_g| >= a (since g owns an a-set), #pinned * a <~ n + binom-overlap => #pinned = O(n/a). At the
binding band a ~ n/2 this gives #pinned = O(1) -- a CONSTANT distinct-g count, i.e. delta* pinned
at the ceiling with NO window-interior gap from this face. If instead a large shared degenerate
core (b) inflates overlaps, the excluded-degenerate structure absorbs it (census-invisible).

MEASURE, exact mod p, PROPER mu_n, p>>n^3, multi-prime, NEVER n=q-1:
For random + structured stacks, at the binding band, enumerate the pinned scalars, compute each
agreement set A_g = maximal g-aligned set, and report:
  - #pinned (distinct-g count)
  - distribution of |A_g|
  - max pairwise |A_g ∩ A_g'| over distinct pinned g,g'  (the packing overlap)
  - whether that max overlap is <= k (claim a) or larger (claim b, with joint-deg<k check)
"""
import itertools, random
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime(n, lo):
    p=lo; p+=(1-p)%n
    if p<3: p=n+1
    while True:
        if p>2 and p%n==1 and all(p%d for d in range(2,int(p**0.5)+1)): return p
        p+=n

def find_g(p,n):
    for h in range(2,20000):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in prime_factors(n)): return x
    raise ValueError

def ddiff(vals,T,xs,p):
    acc=0
    for i in T:
        den=1
        for j in T:
            if i!=j: den=den*((xs[i]-xs[j])%p)%p
        acc=(acc+vals[i]*pow(den,-1,p))%p
    return acc

def agreement_set(u0,u1,gamma,xs,p,k):
    """maximal g-aligned set: coords i where the g-pencil is explained by a deg<k codeword.
    Equivalent characterization via residuals: i is in A_g iff there's a deg<k poly matching
    (u0+g u1) at i and on a spanning context. We approximate A_g as the largest set S s.t. every
    (k+1)-tuple in S has residual(pencil)=0. Build greedily: pencil w = u0 + g u1; A_g = {i : i lies
    on the deg<k interpolant of w through any k+1 of the 'good' coords}. Cleanest exact route:
    A_g = max set with all (k+1)-tuple residuals of w zero. Compute by: residual_w over all (k+1)
    tuples, a coord i is 'consistent' if removing the obstruction... -> use the agreementSet defn:
    fix the global deg<k interpolant? No single one. Use: S is g-aligned iff w|S is deg<k. The
    MAXIMAL such S = union of all g-aligned (k+1)-tuples that pairwise extend. Practical exact:
    A_g = {i : w restricted to (some k coords) ∪ {i} stays deg<k consistent}. We compute the maximal
    aligned set by taking the deg<k interpolant through the FIRST k+1 aligned coords and collecting
    all coords matching it (this is agreementSet of that explainer = maximal, per AgreementSetMaximal).
    """
    n=len(xs)
    w=[(u0[i]+gamma*u1[i])%p for i in range(n)]
    # find a (k+1)-tuple with zero residual to seed the explainer
    best=set()
    for T in itertools.combinations(range(n),k+1):
        if ddiff(w,T,xs,p)==0:
            # interpolate deg<k poly through T (k+1 pts, but deg<k => k coeffs => overdetermined by 1;
            # residual=0 means consistent). Use first k pts to define the deg<k interpolant, then
            # collect all matching coords (= agreementSet of that explainer = maximal).
            ctx=list(T)[:k]
            # Lagrange deg-(k-1) interpolant through ctx
            def interp(x):
                s=0
                for a in ctx:
                    num=1; den=1
                    for b in ctx:
                        if a!=b:
                            num=num*((x-xs[b])%p)%p; den=den*((xs[a]-xs[b])%p)%p
                    s=(s+w[a]*num*pow(den,-1,p))%p
                return s
            S=set(i for i in range(n) if w[i]==interp(xs[i]))
            if len(S)>len(best): best=S
    return best

def run(n,k,beta_lo,n_stacks=6):
    p=find_prime(n,max(beta_lo,n**3))
    g=find_g(p,n)
    xs=[pow(g,i,p) for i in range(n)]
    a=n//2  # binding band
    random.seed(7)
    rows=[]
    for trial in range(n_stacks):
        if trial==0:
            u0=[pow(x,n//2,p) for x in xs]; u1=[pow(x,n//2-1,p) for x in xs]; lbl="binderline"
        else:
            u0=[random.randrange(p) for _ in range(n)]; u1=[random.randrange(p) for _ in range(n)]; lbl=f"rand{trial}"
        # pinned scalars: g s.t. exists non-degenerate g-aligned a-set. Scan gamma over a sample
        # (full field too big); use the residual-ratio pins from non-degenerate (k+1)-tuples.
        Tlist=list(itertools.combinations(range(n),k+1))
        e0={T:ddiff(u0,T,xs,p) for T in Tlist}
        e1={T:ddiff(u1,T,xs,p) for T in Tlist}
        # candidate gammas = the pins -e0/e1 from non-degenerate tuples
        cand=set()
        for T in Tlist:
            if e1[T]!=0:
                cand.add((-e0[T]*pow(e1[T],-1,p))%p)
        pinned=[]; Asets={}
        for gamma in cand:
            A=agreement_set(u0,u1,gamma,xs,p,k)
            # pinned iff it owns a non-degenerate a-set: needs |A|>=a AND a non-degenerate (k+1)-tuple
            if len(A)>=a:
                # check non-degeneracy: some (k+1)-tuple in A with not both residuals 0
                nd=False
                for T in itertools.combinations(sorted(A),k+1):
                    if not (e0[T]==0 and e1[T]==0): nd=True; break
                if nd:
                    pinned.append(gamma); Asets[gamma]=A
        # packing: max pairwise overlap
        maxov=0; ov_jointdeg=None
        pl=list(pinned)
        for i in range(len(pl)):
            for j in range(i+1,len(pl)):
                inter=Asets[pl[i]]&Asets[pl[j]]
                if len(inter)>maxov:
                    maxov=len(inter)
                    # is the intersection jointly deg<k?
                    jd = all(e0[T]==0 and e1[T]==0 for T in itertools.combinations(sorted(inter),k+1)) if len(inter)>=k+1 else True
                    ov_jointdeg=jd
        sizes=sorted(len(A) for A in Asets.values())
        rows.append((lbl,len(pinned),sizes[:6],maxov,ov_jointdeg))
    return p,a,rows

if __name__=="__main__":
    for n in [8,12,16]:
        k=2
        p,a,rows=run(n,k,n**3, n_stacks=5)
        print(f"\n=== n={n} k={k} a(band)={a} p={p} ===")
        print(f"  {'stack':>11} {'#pinned':>8} {'|A_g| sizes':>16} {'maxOverlap':>10} {'overlap<=k?':>11} {'jointdeg?':>9}")
        for lbl,np_,sizes,maxov,jd in rows:
            print(f"  {lbl:>11} {np_:>8} {str(sizes):>16} {maxov:>10} {str(maxov<=k):>11} {str(jd):>9}")
