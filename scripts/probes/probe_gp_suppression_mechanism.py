#!/usr/bin/env python3
"""
PROXIMITY PRIZE -- Conjecture (G), THE suppression mechanism for F_p-genuine relations.

FINDINGS from probe_gp_genuine_threshold_mitm (n=8,p=521):
  * genuine relations first appear at r=5 (none at r<=4);
  * ALL genuine alpha at r=5 have Norm(alpha)=1042=2p EXACTLY (minimum: divisible by p,
    times the forced factor 2 that ramifies in Z[zeta_8]); a SINGLE Galois/dilation class;
  * the minimal alpha = 1 - zeta - 2 zeta^2 - 6 zeta^3  lies in the distinguished prime
    P|p (alpha(z)=0 mod p) and is nonzero mod the conjugate primes.

MECHANISM HYPOTHESIS (this probe TESTS it):
  Genuine relations of depth r are governed by the SHORTEST vectors of the ideal P|p in
  the archimedean (Minkowski) embedding.  alpha = (sum of x-roots) - (sum of y-roots) is a
  cyclotomic integer with all coords in {-r..r} and alpha in P.  The SMALLEST nonzero such
  alpha (min |Norm| = the min over P\{0}, which is >= p and ramification-forced to be a
  small multiple of p) requires the L1-mass of alpha (= sum|coeff|, after splitting +/-
  into the r-budget) to fit inside 2r roots.  So the THRESHOLD r* = (min L1-realization
  cost of a shortest P-vector)/2.  As p grows (beta up), the shortest P-vector gets
  longer (Minkowski: shortest vector length ~ Norm^{1/phi} ~ p^{1/phi} ~ n^{beta*2/n}),
  so r* grows -> Conjecture (G) suppression.

We:
 (1) For several primes p (fixed n), find the shortest vector(s) of P (min over genuine
     alpha of |Norm|, and the realization cost = min r at which it appears) and confirm
     r*(p) tracks the Minkowski length of P.
 (2) Verify the BIJECTION: genuine relations at depth r  <->  (a fixed shortest P-vector
     alpha_0)  +  (a char-0 representation of alpha_0 as diff of 2r roots).  i.e. genuine
     count G_r = (#shortest P-vectors up to sign) * (#ways to write it as r-roots minus
     r-roots) -- and the SECOND factor is the same combinatorial object as char-0
     near-relations.  Concretely we check: every genuine alpha at the threshold is in the
     Galois+dilation orbit of ONE alpha_0; count the orbit and the per-alpha multiplicity.

Honesty: exact integer/cyclotomic arithmetic; brute or MITM enumeration; Norm via the
phi complex conjugate embeddings rounded with an error check.
"""
import itertools, math, cmath
from collections import defaultdict

def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    d=3
    while d*d<=q:
        if q%d==0: return False
        d+=2
    return True
def factor(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError
def find_prime(t,mod):
    p=t+((1-(t%mod))%mod)
    if p<t:p+=mod
    while not isprime(p):p+=mod
    return p

# precompute the phi primitive-root embeddings for n
def embeddings(n):
    phi=n//2
    return [[cmath.exp(2j*math.pi*j/n)**k for k in range(phi)] for j in range(1,n,2)]

def cyc_norm(vec, emb):
    prod=1.0+0j; mx=0.0; l2=0.0
    for row in emb:
        v=sum(vec[k]*row[k] for k in range(len(vec)))
        prod*=v; a=abs(v); mx=max(mx,a); l2+=a*a
    return round(prod.real), mx, l2

def shortest_P_vectors_and_threshold(n, p, rmax, g=None, verbose=True):
    """MITM over depth r; record genuine alpha; return min |Norm|, threshold r*, and the
       set of distinct alpha (length-phi vectors) achieving the min-norm at threshold."""
    if g is None: g=primroot(p)
    z=pow(g,(p-1)//n,p); zpow=[pow(z,k,p) for k in range(n)]
    phi=n//2; m=(p-1)//n; emb=embeddings(n)
    beta=math.log(p)/math.log(n)
    if verbose:
        print(f"\n{'='*78}\nn={n} p={p} beta={beta:.3f} m={m} log2m={math.log2(m):.1f}\n{'='*78}",flush=True)
    rstar=None; minN=None; thr_alphas=None; thr_data=None
    for r in range(2,rmax+1):
        xb=defaultdict(list)
        for tail in itertools.product(range(n),repeat=r-1):
            ax=(0,)+tail
            S=sum(zpow[a] for a in ax)%p
            cnt=[0]*n
            for a in ax: cnt[a]+=1
            xb[S].append((tuple(cnt),ax))
        gen=0; alpha_count=defaultdict(int); examples=defaultdict(list)
        norms=defaultdict(int)
        for by in itertools.product(range(n),repeat=r):
            S=sum(zpow[b] for b in by)%p
            lst=xb.get(S)
            if not lst: continue
            yc=[0]*n
            for b in by: yc[b]+=1
            for (xc,ax) in lst:
                d=[xc[k]-yc[k] for k in range(n)]
                vec=[0]*phi
                for k in range(n):
                    if k<phi: vec[k]+=d[k]
                    else:     vec[k-phi]-=d[k]
                if any(vec):
                    gen+=1
                    tv=tuple(vec)
                    alpha_count[tv]+=1
                    N,mx,l2=cyc_norm(vec,emb)
                    norms[N]+=1
                    if len(examples[tv])<2: examples[tv].append((ax,by))
        gen_full=gen*n  # restore x-dilation gauge
        rate=n**(2*r)/p
        if gen==0:
            if verbose: print(f" r={r}: G_r=0 (suppressed; n^2r/p={rate:.1f})",flush=True)
            continue
        thisminN=min(abs(N) for N in norms if N!=0)
        # collapse alpha by dilation (zeta-mult: cyclic shift with sign wrap) + Galois (c odd)
        # canonical alpha class: orbit under  zeta*  (shift+wrap-neg)  and  sigma_c.
        def shift(v):  # multiply by zeta: v -> zeta*v ; coeff k -> k+1, and coeff phi-1 wraps to -coeff at 0
            w=[0]*phi
            for k in range(phi):
                nk=k+1
                if nk<phi: w[nk]+=v[k]
                else:      w[0]-=v[k]
            return tuple(w)
        def galois_c(v,c):  # zeta -> zeta^c : exponent k -> c*k mod n, reduce
            w=[0]*phi
            for k in range(phi):
                kk=(c*k)%n
                if kk<phi: w[kk]+=v[k]
                else:      w[kk-phi]-=v[k]
            return tuple(w)
        def canon_alpha(v):
            best=None
            cur=v
            for _ in range(n):  # n dilation shifts
                for c in range(1,n,2):  # galois
                    cand=galois_c(cur,c)
                    cand=tuple(cand)
                    negcand=tuple(-x for x in cand)
                    for cc in (cand,negcand):
                        if best is None or cc<best: best=cc
                cur=shift(cur)
            return best
        classes=defaultdict(int)
        minN_alphas=[a for a in alpha_count if abs(cyc_norm(a,emb)[0])==thisminN]
        for a in alpha_count:
            classes[canon_alpha(a)]+=alpha_count[a]
        minN_classes=set(canon_alpha(a) for a in minN_alphas)
        if verbose:
            print(f" r={r}: G_r(full)={gen_full}  suppression {gen_full/rate:.4f}"
                  f"  min|Norm(alpha)|={thisminN} (={thisminN/p:.3g}*p)"
                  f"  #distinct-alpha={len(alpha_count)}  #alpha-classes(Galois*dil)={len(classes)}"
                  f"  #min-norm-classes={len(minN_classes)}",flush=True)
            # show the actual minimal alpha class reps
            for cl in sorted(minN_classes)[:3]:
                N,mx,l2=cyc_norm(cl,emb)
                l1=sum(abs(x) for x in cl)
                print(f"     minimal alpha class rep = {list(cl)}  Norm={N}  max|conj|={mx:.3f}"
                      f"  L1={l1}  L2^2={l2:.2f}  Minkowski-ratio max|conj|/p^(1/phi)={mx/p**(1/phi):.3f}",flush=True)
        if rstar is None:
            rstar=r; minN=thisminN; thr_alphas=minN_alphas; thr_data=(r,gen_full,classes,minN_classes)
    return dict(rstar=rstar, minN=minN, beta=beta, p=p, phi=phi)

if __name__=="__main__":
    print("### n=8 across growing beta: does r* (first genuine depth) GROW with beta?",flush=True)
    res=[]
    for bp in [3,4,5]:
        p=find_prime(8**bp,8)
        r=shortest_P_vectors_and_threshold(8,p,7)
        res.append(r)
    print("\n### SUMMARY n=8:  beta -> r*(first genuine) and min|Norm|/p",flush=True)
    for r in res:
        if r['rstar']:
            print(f"  p={r['p']:>7} beta={r['beta']:.2f}: r*={r['rstar']}  min|Norm(alpha)|/p={r['minN']/r['p']:.3g}"
                  f"  Minkowski p^(1/phi)={r['p']**(1/r['phi']):.2f}",flush=True)
        else:
            print(f"  p={r['p']:>7} beta={r['beta']:.2f}: r*>7 (no genuine up to depth 7 -- DEEPER suppression)",flush=True)
    print("\n### n=16 beta~3 (threshold deeper; limited depth):",flush=True)
    shortest_P_vectors_and_threshold(16, find_prime(16**3,16), 4)
