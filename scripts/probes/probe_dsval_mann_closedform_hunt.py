#!/usr/bin/env python3
"""
probe_dsval_mann_closedform_hunt.py   (#407 A5 -- closed-form hunt from antipodal structure)

We've VERIFIED (probe_dsval_mann_antipodal_orbit_count2.py) that delta* boundary
witnesses for n=8 are FULLY ANTIPODAL-PAIRED cyclotomic-coset sets (Mann), and the
exact char-0 delta* matches issue ground truth.  Now PIN the closed form.

This probe does a FAST, targeted computation for n=8,16,32 (rho=1/4,1/2):
  * For each far direction (a,b), the candidate bad gammas come from agreement sets
    that are MANN-STRUCTURED: S = union of cyclotomic cosets of mu_n.  By Mann/Lam-Leung
    (n=2^a), every consistent agreement set is a disjoint union of antipodal pairs
    {zeta,-zeta} (+ possibly the fixed points {1} and/or {-1} as Phi_1,Phi_2 singletons).
  * We DIRECTLY enumerate Mann-structured candidate agreement sets S (unions of
    cyclotomic cosets) of each size w, and for each test whether some far pencil
    (a,b,gamma) has S as agreement set (=> the per-S gamma is forced & unique generically).
  * Count distinct gammas per w -> I(w) -> delta*.  Then read closed form.

The cyclotomic cosets of mu_n (n=2^a), as INDEX sets in {0..n-1} (mu[i]=zeta^i):
  level j (1<=j<=a): coset C_j = { i : v2(i)=a-j } has size 2^{j-1}; these are the
  roots of Phi_{2^j}.  Plus C_0 = {0} (root of Phi_1, i.e. zeta^0=1).
  Antipodal map i -> i+n/2.  Each C_j (j>=2) is antipodal-closed; C_1={n/2} is the
  single fixed antipode (-1); C_0={0} is +1.

A Mann-structured S = union of a chosen set of these cosets.  Total cosets: C_0,
C_1, C_2,...,C_a with sizes 1,1,2,4,...,2^{a-1}.  Number of distinct sizes-of-union
is small -> we enumerate all 2^{a+1} unions.

For each union S, the pencil x^a+gamma x^b agrees with deg<k g on S iff the
(k+2)-col generalized Vandermonde [1,x,...,x^{k-1}, x^a, x^b] restricted to S has the
(x^a, gamma) relation in deg<k span.  We solve for the gamma(s) making S consistent
and count -- EXACT over p>>n^4.
"""
import itertools, sys
from math import gcd, log2
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def find_prime_1_mod_n(n,lo):
    p=lo+(n-(lo%n))+1
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=n
def primitive_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def roots_of_unity(p,n):
    g=primitive_root(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def v2(x):
    if x==0: return 99
    c=0
    while x%2==0: x//=2; c+=1
    return c

def cyclotomic_cosets(n):
    a=int(round(log2(n)))
    cosets=[]
    # C_0 = {0}; level j (1..a): {i: v2(i)=a-j}
    cosets.append([0])
    for j in range(1,a+1):
        cosets.append([i for i in range(1,n) if v2(i)==a-j])
    return cosets  # sizes 1,1,2,4,...,2^{a-1}

def rank_mod_p(M,p):
    M=[row[:] for row in M]; rows=len(M); cols=len(M[0]) if rows else 0
    r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i][c]%p!=0: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        inv=pow(M[r][c],p-2,p)
        M[r]=[(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]%p!=0:
                f=M[i][c]
                M[i]=[(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows: break
    return r

def gammas_for_S(mu,a,b,S,k,p):
    """All gamma s.t. x^a+gamma x^b deg<k-interpolable on S.
       Condition: for the matrix V=[x^j: j<k | x^a | x^b] on S (|S| rows, k+2 cols),
       the vector x^a on S plus gamma*(x^b on S) lies in deg<k column span.
       i.e. exists deg<k coeffs c with sum c_j x^j = x^a + gamma x^b on S.
       Treat as linear system in (c_0..c_{k-1}, gamma).  Solve; gamma may be:
         - forced unique, - free (any), - none. Return ('all',) / set of gammas / empty.
    """
    Sl=sorted(S); w=len(Sl)
    if w<=k: return ('all',)   # trivially interpolable for any gamma
    # unknowns c_0..c_{k-1}, gamma : equations  sum_j c_j x_i^j - gamma x_i^b = x_i^a
    M=[]; rhs=[]
    for i in Sl:
        x=mu[i]
        row=[pow(x,j,p) for j in range(k)] + [(-pow(x,b,p))%p]
        M.append(row); rhs.append(pow(x,a,p))
    # augmented solve: find gamma values consistent. Variables: k + 1 (gamma).
    # Gaussian eliminate; if system consistent uniquely -> one gamma; if gamma free -> 'all'
    aug=[M[i][:]+[rhs[i]] for i in range(w)]
    nvar=k+1
    # eliminate
    r=0; pivcol=[]
    for c in range(nvar):
        piv=None
        for i in range(r,w):
            if aug[i][c]%p!=0: piv=i;break
        if piv is None: continue
        aug[r],aug[piv]=aug[piv],aug[r]
        inv=pow(aug[r][c],p-2,p)
        aug[r]=[(x*inv)%p for x in aug[r]]
        for i in range(w):
            if i!=r and aug[i][c]%p!=0:
                f=aug[i][c]; aug[i]=[(aug[i][j]-f*aug[r][j])%p for j in range(nvar+1)]
        pivcol.append(c); r+=1
        if r==w: break
    # check inconsistency rows
    for i in range(r,w):
        if aug[i][nvar]%p!=0 and all(aug[i][j]%p==0 for j in range(nvar)):
            return set()  # inconsistent: no gamma
    # gamma column index = k
    if k in pivcol:
        # gamma determined by free vars? gamma pivot row gives gamma = const - (free terms)
        # if there are free non-gamma vars, gamma could still be forced if its row has no free
        prow=pivcol.index(k)
        # gamma = rhs - sum over free cols. If any free col has nonzero coeff in this row -> gamma not unique
        freecols=[c for c in range(nvar) if c not in pivcol]
        if any(aug[prow][c]%p!=0 for c in freecols):
            return ('all',)   # gamma can vary -> infinitely many
        return { aug[prow][nvar]%p }
    else:
        # gamma is a free variable -> any gamma works (all c determined up to it) but need
        # consistency: it's free => 'all'
        return ('all',)

def main():
    cases=[(8,2),(8,4),(16,4),(16,8),(32,8),(32,16)]
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    for (n,k) in cases:
        rho=k/n
        p=find_prime_1_mod_n(n,n**4*4)
        mu=roots_of_unity(p,n)
        budget=n
        cosets=cyclotomic_cosets(n)
        ncos=len(cosets)
        # all Mann-structured unions S (nonempty)
        unions=[]
        for mask in range(1,1<<ncos):
            S=[]
            for j in range(ncos):
                if mask&(1<<j): S+=cosets[j]
            unions.append(frozenset(S))
        # per direction, per S: gammas
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
        # results[w] = (max distinct-gamma count over dirs, dir)
        results=defaultdict(lambda:(0,None))
        for (a,b) in dirs:
            # for each w, set of gammas s.t. SOME S of size>=w consistent.
            # We collect, per gamma, the max consistent |S|.
            gamma_maxw=defaultdict(int)
            for S in unions:
                w=len(S)
                if w<=k: continue
                res=gammas_for_S(mu,a,b,S,k,p)
                if res==('all',):
                    # degenerate direction; record as 'all' marker - skip (not a finite bad set)
                    continue
                for g in res:
                    if w>gamma_maxw[g]: gamma_maxw[g]=w
            for w in range(k+1,n+1):
                c=sum(1 for g,mw in gamma_maxw.items() if mw>=w)
                if c>results[w][0]: results[w]=(c,(a,b))
        ws=sorted(results)
        w_min=next((w for w in ws if results[w][0]<=budget),None)
        ds=1-w_min/n if w_min else None
        print(f"\n=== n={n} k={k} rho={rho} p={p} budget={budget} (Mann-coset enumeration) ===")
        for w in sorted(results,reverse=True):
            c,d=results[w]
            mk=" <== boundary" if w==w_min else ""
            print(f"   w={w:2d} delta={1-w/n:.4f}  I={c:4d}  dir={d}{mk}")
        if ds is not None:
            g=gt.get((n,k))
            print(f"  delta*={ds:.4f}  n*delta*={n*ds}  gt={g}  MATCH={(abs(ds-g)<1e-9) if g else '?'}")
            print(f"  w_min={w_min} n-w_min={n-w_min}  c=(1-rho-d*)log2 n={(1-rho-ds)*log2(n):.4f}")

if __name__=="__main__":
    main()
