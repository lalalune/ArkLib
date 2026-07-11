#!/usr/bin/env python3
"""
B1 REALIZABILITY LEVER (the central claim): does "S = roots of ONE deg-<k poly" reduce |S|
below the generic (k+2)-sparse root-count budget?

Two objects for a FIXED direction (a,b) over mu_n, RS[k]:

(1) GENERIC count budget G(a,b):
    max over gamma, over ALL deg-<k P, of #{x in mu_n: x^a + gamma x^b - P(x) = 0}.
    But that IS the realizability object. The "generic / circulant-of-counts" object that B1
    says discards realizability is instead:
      G_circ(a,b) = max #roots in mu_n a (k+2)-SPARSE poly with support {0..k-1,a,b} can have,
      WITHOUT requiring the {0..k-1} part to be a single fixed interpolation -- i.e. allowing
      the low-degree coefficients to be CHOSEN PER-ROOT-SET. The count-level upper bound treats
      each potential agreement set independently; the realizability constraint forces ONE P.

   Concretely the circulant/count bound is the BEZOUT/degree bound: a nonzero (k+2)-sparse poly
   has <= deg = max(a, b) roots, but restricted to mu_n the SPARSE structure caps it lower.
   We compute the max #roots-in-mu_n over ALL polys supported on {0..k-1,a,b} (free coeffs),
   = the largest subset S of mu_n such that the vandermonde-like system
        [ x^0 ... x^{k-1}  x^a  x^b ]  (rows x in S)  has a nonzero kernel vector with the
        x^a-coeff and x^b-coeff NOT both zero... actually any S of size <= k+2-1 = k+1 admits a
        sparse poly vanishing on it (kernel of (k+2) columns, |S| rows: nonzero kernel if |S|<k+2).
   So G_sparse_free = up to ... we instead measure: largest S subset mu_n s.t. there's a poly
   with support {0..k-1,a,b}, nonzero, vanishing on all of S, AND with x^a coeff = 1 (monic top),
   x^b coeff = gamma (free). That's |S| <= k+1 generically (square+1 system) UNLESS the columns
   are dependent on mu_n. This is the "count" object.

(2) REALIZABILITY object R(a,b) = max_agreement (our exact computation): the deg-<k tail must be
    a genuine single polynomial = interpolating codeword, top is fixed x^a+gamma x^b.
    This is EXACTLY what we computed; R(a,b) = max over gamma of max-agreement.

The B1 claim: R(a,b)  <  G_circ(a,b) strictly (realizability is a real constraint). We test it.

We compute G_circ exactly: max size S subset mu_n admitting a poly p with support in {0..k-1}U{a,b},
p != 0, p|_S = 0. Equivalently rank of the |S| x (k+2) evaluation matrix < |S| (so kernel nonzero).
Max such |S| = max S with rank(M_S) < |S|, M_S columns = [x^0..x^{k-1}, x^a, x^b].
Over a field, generic |S| <= k+2 columns => rank <= k+2, so |S| up to k+2 can be deficient...
Actually ANY |S| <= k+1 has a nonzero kernel automatically (more columns than... no: |S| rows,
k+2 cols; nonzero kernel if columns dependent: if |S| < k+2 then k+2 cols of length |S| => rank<=|S|<k+2
so kernel dim>=2>0, always nonzero kernel). So G_circ >= up to k+1 trivially, and beyond that requires
special dependency on mu_n. We find the MAX |S| with a nonzero sparse kernel, by searching subsets.

To keep it exact and feasible we compute G_circ by the matroid/rank route over all subsets up to size
n, using that S works iff rank of full mu_n evaluation matrix restricted... we just test increasing s.
"""
import itertools, math
import numpy as np
from sympy import isprime, factorint, Matrix

def find_prime(n,want_min):
    p=max(want_min,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n

def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c

def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def matrank_modp(rows, p):
    """rank over F_p of an integer matrix (list of rows)."""
    A=[r[:] for r in rows]
    R=len(A);
    if R==0: return 0
    C=len(A[0]); rank=0; col=0
    for col in range(C):
        piv=None
        for r in range(rank,R):
            if A[r][col]%p!=0: piv=r;break
        if piv is None: continue
        A[rank],A[piv]=A[piv],A[rank]
        inv=pow(A[rank][col]%p,p-2,p)
        A[rank]=[(x*inv)%p for x in A[rank]]
        for r in range(R):
            if r!=rank and A[r][col]%p!=0:
                f=A[r][col]%p
                A[r]=[(A[r][c]-f*A[rank][c])%p for c in range(C)]
        rank+=1
        if rank==R: break
    return rank

def G_circ(a,b,xs,k,p):
    """max |S| subset mu_n with a NONZERO poly supported on {0..k-1,a,b} vanishing on S.
       support columns: exponents E = sorted({0..k-1} U {a,b}). #cols = t (<=k+2).
       S works iff rank(M_S) < t? No: nonzero kernel of M_S^T? We need coeff vector v (len t)!=0
       with M_S v = 0, i.e. v in right-kernel of M_S (|S| x t). Nonzero kernel iff rank(M_S) < t.
       So we want max |S| with rank(M_S) < t. Since rank <= min(|S|,t), if |S| big rank can be t.
       Max |S| with rank<t : start from full set, this is the max # points that fit < t-dim space.
       = n - (min # points to force rank=t). We just compute: the max subset with rank<t.
       Equivalent: t-dim column space; points x give vectors v_x=[x^e for e in E] in F_p^t.
       max |S| with the {v_x: x in S} spanning a <t-dim space => they lie in a hyperplane =>
       a sparse poly vanishes on them. So G_circ = max # of the n vectors v_x lying in a common
       proper subspace = n - min#outside. = largest # in a hyperplane (codim-1). We compute the
       max over all hyperplanes = max # x with c.v_x=0 for some nonzero c = max #roots over all
       sparse polys = what we want. Compute by: for the realized polys it's <=, but the MAX is the
       largest agreement of x^a (or any) ... we brute over candidate vanish-sets via rank test on
       increasing sizes is expensive; instead = max over nonzero c of #{x: sum c_e x^e=0}.
       We sample c? No -- do it exactly: the max #roots of a t-sparse poly in mu_n.
       Brute: enumerate subsets is 2^n. For n<=16 we can do smarter: it's the covering radius style.
       We do: the max #roots = n - dmin of the [n, t]-'sparse-generator' code? messy.
       Pragmatic exact for small n: enumerate hyperplanes via choosing t-1 points to define one,
       then count. max |S| = max over (t-1)-subsets B of (#x in mu_n on the hyperplane spanned).
    """
    E=sorted(set(list(range(k))+[a,b]))
    t=len(E)
    V=[[pow(x,e,p) for e in E] for x in xs]  # n x t
    n=len(xs)
    best=0
    # a sparse poly vanishing on S <=> coeff c (len t) nonzero, V[x].c=0 for x in S.
    # max |S| = max over nonzero c of #{x: V[x].c=0}. Parameterize c by its kernel from (t-1) pts.
    # choose (t-1) points -> 1-dim solution space for c (generically) -> count zeros.
    from itertools import combinations
    idx=list(range(n))
    for B in combinations(idx,t-1):
        # solve V[B] c = 0, c in F_p^t, expect 1-dim kernel
        M=[V[i][:] for i in B]
        # find a nonzero kernel vector via gaussian elim
        c=kernel_vec(M,t,p)
        if c is None: continue
        cnt=sum(1 for x in range(n) if sum(V[x][j]*c[j] for j in range(t))%p==0)
        if cnt>best: best=cnt
        if best==n: break
    return best, t

def kernel_vec(M, t, p):
    """one nonzero vector in right-kernel of M (rows length t)."""
    A=[r[:] for r in M]; R=len(A)
    pivcol={}; rank=0; rowof=[]
    A=[ [x%p for x in r] for r in A]
    col=0; prow=0
    pivot_cols=[]
    r=0
    for c in range(t):
        piv=None
        for rr in range(r,R):
            if A[rr][c]%p!=0: piv=rr;break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c]%p,p-2,p); A[r]=[(x*inv)%p for x in A[r]]
        for rr in range(R):
            if rr!=r and A[rr][c]%p!=0:
                f=A[rr][c]%p; A[rr]=[(A[rr][cc]-f*A[r][cc])%p for cc in range(t)]
        pivot_cols.append(c); r+=1
        if r==R: break
    free=[c for c in range(t) if c not in pivot_cols]
    if not free: return None
    fc=free[0]; c=[0]*t; c[fc]=1
    for ri,pc in enumerate(pivot_cols):
        c[pc]=(-A[ri][fc])%p
    return c

def worst_over_gamma_agree(a,b,xs,k,p,sample=80):
    import itertools as it
    G=list(range(1,p))
    if len(G)>sample:
        step=max(1,(p-1)//sample); G=list(range(1,p,step))
    n=len(xs); xa=np.array(xs,dtype=object); best=0
    def maxagree(fv):
        bb=k
        fa=np.array(fv,dtype=object)
        for T in it.combinations(range(n),k):
            Tl=list(T); vals=np.zeros(n,dtype=object)
            for tt in Tl:
                xt=xs[tt]; num=np.ones(n,dtype=object); den=1
                for s in Tl:
                    if s==tt: continue
                    num=(num*((xa-xs[s])%p))%p; den=(den*((xt-xs[s])%p))%p
                vals=(vals+(fv[tt]*num)%p*pow(den%p,p-2,p))%p
            ag=int(np.sum(vals%p==fa%p))
            if ag>bb: bb=ag
            if bb==n: return n
        return bb
    for g in G:
        fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
        s=maxagree(fv)
        if s>best: best=s
    return best

def main():
    print("="*120)
    print("B1 REALIZABILITY LEVER: realizable max|S| (one fixed codeword)  vs  G_circ (count-level sparse budget)")
    print("="*120)
    for (n,k) in [(8,2),(8,4),(12,3),(16,4)]:
        if k>=n-1: continue
        p=find_prime(n,n*40+1)
        xs,w=mu_n(p,n); m=(p-1)//n; rho=k/n
        print(f"\n### n={n} k={k} p={p} m={m} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###")
        print(f"{'a':>3}{'b':>3}{'d':>3} | {'realiz_maxS':>11} {'G_circ':>7} {'t=#supp':>7}  gap=Gcirc-realiz")
        rows=[]
        for a in range(k,n):
            for b in range(0,a):
                d=math.gcd(a-b,n)
                R=worst_over_gamma_agree(a,b,xs,k,p)
                Gc,t=G_circ(a,b,xs,k,p)
                rows.append((a,b,d,R,Gc,t))
        # print worst few by realizable, and the max gap
        rows.sort(key=lambda r:-r[3])
        for r in rows[:6]:
            print(f"{r[0]:>3}{r[1]:>3}{r[2]:>3} | {r[3]:>11} {r[4]:>7} {r[5]:>7}  gap={r[4]-r[3]}")
        maxgap=max(rows,key=lambda r:r[4]-r[3])
        worstR=max(rows,key=lambda r:r[3])
        worstG=max(rows,key=lambda r:r[4])
        print(f"  >>> max realizable maxS = {worstR[3]} (a={worstR[0]},b={worstR[1]},d={worstR[2]});  "
              f"max G_circ = {worstG[4]} (a={worstG[0]},b={worstG[1]});  max(Gcirc-realiz) gap = {maxgap[4]-maxgap[3]}")

if __name__=="__main__":
    main()
