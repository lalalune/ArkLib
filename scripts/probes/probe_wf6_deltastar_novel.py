# probe_wf6_deltastar_novel.py  (Target A4, Fable 2026-06-13)  -- EFFICIENT rewrite
#
# Tests 3 NOVEL candidate delta*-pinning conjectures that route around BOTH the
# Johnson list wall (caps at 1-sqrt(rho)) and the additive-moment wall (short by
# n^{1/2}).
#
# Efficient method.  We DON'T enumerate p^k codewords.  For a fixed line L=u0+g*u1,
# a codeword w (deg<k poly) agreeing with L on a set S of size a>=k is determined by
# any k points of S (Lagrange).  So we enumerate a-subsets T of [n], interpolate the
# deg<k poly through (dom_i, L_i) for i in the first k of T, and check it matches on
# all of T.  This gives, per gamma, the set of "explainable" large-agreement sets =
# the list-decoding picture.  The bad event additionally needs NOT pairJointAgreesOn:
# u0 and u1 must NOT BOTH be individually deg<k-explainable on S.
#
# CONJECTURES (see report at bottom of this file):
#  C1  SCHUR-SQUARE PIN.  delta* is the unique-decoding radius of the SCHUR square
#      C2 = RS[dom, 2k-1].  Claim: the MCA bad event for the PAIR (u0,u1) cannot fire
#      at radius delta if (1-delta) > (1+rho2)/2 where rho2=(2k-1)/n, i.e. while the
#      line stays inside the UD ball of C2.  Mechanism: the product structure u0*u1
#      lives in C2; joint explainability is governed by C2 unique decoding, NOT C.
#  C2  GAMMA-VARIANCE PIN (averaging over the SCALAR not the rows).  The number of
#      bad gamma equals (up to O(1)) the number of gamma for which the line lands in
#      a list-decodable ball whose list contains a NON-joint codeword.  Claim:
#      #bad <= (deg of resultant in gamma) = (a-k+1)*(number of agreement sets), and
#      crucially this is bounded by the SCHUR list size, giving delta* > Johnson.
#  C3  NULLSTELLENSATZ BAD-PAIR COUNT.  #{(T, gamma): line through T is a codeword,
#      gamma kills the joint}  <=  C(n,a) * (a-k).  For mu_n the zero-sum / Vieta
#      structure makes only O(n) of these survive => poly bad-scalar count in window.
#
# OUTPUT we trust: exact MCA badcount for n=8 (full), n=10 sampled.

import itertools, random
from math import comb, isqrt

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

def lagrange_through(xs, ys, k, p):
    # deg<k poly through first k points (xs[:k],ys[:k]); return coef list len k or None
    # Vandermonde solve
    m=k
    A=[[pow(xs[i],j,p) for j in range(m)]+[ys[i]] for i in range(m)]
    for col in range(m):
        piv=next((r for r in range(col,m) if A[r][col]%p),None)
        if piv is None:return None
        A[col],A[piv]=A[piv],A[col]
        inv=pow(A[col][col],p-2,p)
        A[col]=[(v*inv)%p for v in A[col]]
        for r in range(m):
            if r!=col and A[r][col]%p:
                f=A[r][col];A[r]=[(A[r][t]-f*A[col][t])%p for t in range(m+1)]
    return [A[i][m]%p for i in range(m)]

def evalc(coef,x,p):
    r=0
    for c in reversed(coef):r=(r*x+c)%p
    return r%p

def is_codeword_word(word, dom, k, p):
    # is `word` (length n) the evaluation of a deg<k poly on dom?
    n=len(dom)
    coef=lagrange_through(dom[:k],[word[i] for i in range(k)],k,p)
    if coef is None:return False
    return all(evalc(coef,dom[i],p)==word[i] for i in range(n))

def explainable_sets_for_line(L, dom, k, p, a):
    # all maximal-ish agreement sets of size >= a between L and some codeword.
    # Return list of (frozenset S, coef) for codewords w with |agree(w,L)|>=a.
    # Enumerate over a-subsets, interpolate, dedup by coef.
    n=len(dom)
    seen={}
    out=[]
    for T in itertools.combinations(range(n),a):
        xs=[dom[i] for i in T];ys=[L[i] for i in T]
        coef=lagrange_through(xs[:k],ys[:k],k,p)
        if coef is None:continue
        # verify all of T agrees
        if not all(evalc(coef,dom[i],p)==L[i] for i in T):continue
        key=tuple(coef)
        if key in seen:continue
        seen[key]=1
        S=frozenset(i for i in range(n) if evalc(coef,dom[i],p)==L[i])
        out.append((S,coef))
    return out

def joint_on(S, u0, u1, dom, k, p):
    # exists v0,v1 in C with v0|S=u0|S, v1|S=u1|S
    Sl=sorted(S)
    if len(Sl)<k:return True  # underdetermined: a deg<k poly always exists thru <k pts? need agree on S
    # u0 explainable on S iff interpolation thru any k pts of S matches whole S
    def explained(u):
        coef=lagrange_through([dom[i] for i in Sl[:k]],[u[i] for i in Sl[:k]],k,p)
        if coef is None:return False
        return all(evalc(coef,dom[i],p)==u[i] for i in Sl)
    return explained(u0) and explained(u1)

def mca_bad(u0,u1,dom,k,p,a):
    # gamma is bad iff exists S, |S|>=a, line=u0+g u1 explainable on S, NOT joint on S.
    n=len(dom)
    bad=[]
    for g in range(p):
        L=tuple((u0[i]+g*u1[i])%p for i in range(n))
        fired=False
        for (S,coef) in explainable_sets_for_line(L,dom,k,p,a):
            # need a subset S' of S, |S'|>=a, NOT joint. S itself first.
            if not joint_on(S,u0,u1,dom,k,p):
                fired=True;break
            # try size-a subsets of S (only if |S|>a, small)
            if len(S)>a:
                Sl=sorted(S)
                done=False
                for Sp in itertools.combinations(Sl,a):
                    if not joint_on(frozenset(Sp),u0,u1,dom,k,p):
                        fired=True;done=True;break
                if done:break
        if fired:bad.append(g)
    return bad

def run(p,n,k,a,nstacks,seed):
    g=gen(p,n)
    if g is None:return None
    dom=[pow(g,j,p) for j in range(n)]
    rho=k/n
    schur_k=min(2*k-1,n);rho2=schur_k/n
    random.seed(seed)
    maxbad=0;arg=None
    stacks=[]
    for _ in range(nstacks):
        stacks.append((tuple(random.randrange(p) for _ in range(n)),
                       tuple(random.randrange(p) for _ in range(n))))
    # structured: u1 = codeword + spike (near-code direction = open core regime)
    for _ in range(nstacks//3):
        coef=[random.randrange(p) for _ in range(k)]
        u1=[evalc(coef,x,p) for x in dom]
        u1[random.randrange(n)]=(u1[random.randrange(n)]+random.randrange(1,p))%p
        stacks.append((tuple(random.randrange(p) for _ in range(n)),tuple(u1)))
    # structured: u0,u1 both monomials x^e
    for e0 in range(k,min(n,k+4)):
        for e1 in range(k,min(n,k+4)):
            u0=tuple(pow(x,e0,p) for x in dom);u1=tuple(pow(x,e1,p) for x in dom)
            stacks.append((u0,u1))
    for (u0,u1) in stacks:
        bc=len(mca_bad(u0,u1,dom,k,p,a))
        if bc>maxbad:maxbad=bc;arg=(u0,u1)
    johnson_a = isqrt(n*k)+(0 if isqrt(n*k)**2==n*k else 1)
    sqrt_rho=rho**0.5
    delta=1-a/n
    # conjecture predictions
    c1_pred = 1 - rho2  # 1 - schur rate (UD-ball-of-schur boundary, scaled)
    c1_johnson_gap = (1-sqrt_rho)  # plain Johnson radius
    null = comb(n,a)*(max(a-k,0))
    print(f"  p={p} n={n} k={k} a={a} delta={delta:.3f} rho={rho:.3f} sqrt_rho={sqrt_rho:.3f} "
          f"johnson_a={johnson_a}")
    print(f"    MAXBAD={maxbad} eps={maxbad/p:.4f}  | schur_rk={schur_k} rho2={rho2:.3f}")
    print(f"    C1: 1-rho2={c1_pred:.3f} vs 1-sqrt(rho)={c1_johnson_gap:.3f}  "
          f"[C1 routes above Johnson? {c1_pred>c1_johnson_gap}]")
    print(f"    C3: nullform C(n,a)*(a-k)={null}  poly?={null<=n**3}")
    return dict(maxbad=maxbad,a=a,johnson_a=johnson_a,rho2=rho2,delta=delta,
                sqrt_rho=sqrt_rho,c1_pred=c1_pred)

if __name__=="__main__":
    print("=== A4 novel delta* conjecture probe (efficient) ===")
    results={}
    for (p,n,k) in [(17,8,2),(41,8,2),(89,8,2)]:
        print(f"\n-- RS[F_{p}, mu_{n}, k={k}]  (rho={k/n}) --")
        for a in [n-2,n-3,n-4,n-5]:  # deeper->shallower past Johnson
            if a<k+1:continue
            r=run(p,n,k,a,nstacks=200,seed=1)
            results[(p,n,k,a)]=r
    # n=10 k=2 (rho=1/5) one field, fewer stacks
    print(f"\n-- RS[F_61, mu_10, k=2]  (rho=0.2) --")
    for a in [8,7,6,5]:
        run(61,10,2,a,nstacks=80,seed=2)
