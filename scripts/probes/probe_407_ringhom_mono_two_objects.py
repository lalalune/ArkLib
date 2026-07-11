#!/usr/bin/env python3
# ============================================================================
# Issue #407 / Proximity Prize δ* program.
# INDEPENDENT VERIFY-OR-REFUTE of the "ring-homomorphism monotonicity" claim
# (lalalune 2026-06-14T08:41 "Cyclic-sieving attack on Schur-vanishing").
#
# THE CLAIM: for the DEPLOYED quantity = distinct bad-SCALAR count per genuine
#   monomial direction (a,b),
#       N = #{ γ_T = −DD_T(x^a)/DD_T(x^b) : T eligible }
#   reduction ℤ[ζ_n] → 𝔽_q is a ring hom, so on bad scalars it is
#   "merge-only + eligibility-shrink-only", giving
#       N(char-p) ≤ N(char-0)  for every genuine direction, scale-independently.
#   Sub-claims: H1 (eligibility ⊆), no-SPLIT, no-NEW char-p-only scalar.
#
# THIS PROBE implements BOTH objects independently and rigorously:
#   (a) divided-difference bad-scalar count N(a,b)  [their object];
#   (b) line-incidence count I(a,b,w)               [the governing-law object].
# char-0 is EXACT via integer arithmetic in ℤ[ζ_n] (n=2^μ ⟹ Φ_n=x^{n/2}+1,
# so ζ^{n/2}=−1 — elements are length-(n/2) integer vectors). char-p is mod q.
#
# DEFINITIONS.
# n=2^μ, RS_k = polys of degree < k, nodes x_i=ζ^i on D=μ_n.
# A genuine monomial direction (a,b): boundary band a,b ≥ k (so both divided
# differences are nontrivial Schur values) and a≠b mod n.
#
# Object (a) — N(a,b): for T⊆{0..n-1}, |T|=k+1, the bad scalar making the
#   (k+1)-node interpolant of x∈{x_t} ↦ x^a+γ x^b drop a degree is
#       γ_T = −DD_T(x^a)/DD_T(x^b),  DD_T(f)=Σ_t f(x_t)/∏_{s≠t}(x_t−x_s).
#   (DD_T(x^c)=h_{c−k}(x_T), complete-homogeneous/Schur value.)
#   T ELIGIBLE iff DD_T(x^b)≠0. N(a,b)=#{distinct finite γ_T : eligible}.
#
# Object (b) — I(a,b,w): for each (k+1)-subset T solve uniquely for (g∈RS_k, γ)
#   with g(x_t)=x_t^b+γ x_t^a on T; measure true agreement #{i:g(x_i)=x_i^b+γ
#   x_i^a}; I(a,b,w)=#{distinct γ : agreement≥w}. (the far-line incidence the
#   governing law I(δ)=max#{α:line δ-close} uses.)
# ============================================================================
import itertools, math
import sympy

# ---------- exact ℤ[ζ_n] arithmetic for n=2^μ (ζ^{n/2} = −1) ----------
class Cyc:
    """Element of ℤ[ζ_n], n=2^μ, as integer vector of length h=n/2 in basis
    1,ζ,...,ζ^{h-1}, with ζ^h = −1."""
    __slots__=('h','c')
    def __init__(self,h,c=None):
        self.h=h
        self.c=[0]*h if c is None else list(c)
    @staticmethod
    def zeta_pow(h,e):
        n=2*h; e%=n
        v=Cyc(h)
        if e<h: v.c[e]=1
        else:   v.c[e-h]=-1
        return v
    def __add__(s,o): return Cyc(s.h,[s.c[i]+o.c[i] for i in range(s.h)])
    def __sub__(s,o): return Cyc(s.h,[s.c[i]-o.c[i] for i in range(s.h)])
    def __mul__(s,o):
        h=s.h; r=[0]*(2*h)
        for i in range(h):
            if s.c[i]==0: continue
            for j in range(h):
                if o.c[j]: r[i+j]+=s.c[i]*o.c[j]
        out=[0]*h
        for d in range(2*h):
            if r[d]==0: continue
            if d<h: out[d]+=r[d]
            else:    out[d-h]-=r[d]   # ζ^{h+t}=−ζ^t
        return Cyc(h,out)
    def is_zero(s): return all(v==0 for v in s.c)
    def __eq__(s,o): return s.c==o.c
    def __hash__(s): return hash(tuple(s.c))

def cyc_one(h):
    v=Cyc(h); v.c[0]=1; return v

def object_a_exact(n,k,a,b):
    """char-0 N(a,b) using exact ℤ[ζ_n]. Dedup distinct γ_T = -A_T/B_T by
    cross-multiplication A_T*B_{T'} == A_{T'}*B_T (sign-consistent)."""
    h=n//2
    xs=[Cyc.zeta_pow(h,i) for i in range(n)]
    xa=[Cyc.zeta_pow(h,(i*a)%n) for i in range(n)]
    xb=[Cyc.zeta_pow(h,(i*b)%n) for i in range(n)]
    # divided difference over ℚ(ζ): represent as (numer in ℤ[ζ], denom in ℤ[ζ]).
    # DD_T(f)=Σ_t f_t / D_t where D_t=∏_{s≠t}(x_t-x_s). Common denom P=∏_t D_t.
    fracs=[]   # list of (num, den) cyclotomic for finite eligible gamma = -na/da reduced to (num,den)=(−A,B) where A=DD(x^a)num etc.
    eligible=0
    for T in itertools.combinations(range(n),k+1):
        m=k+1
        Ds=[]
        for t in range(m):
            D=cyc_one(h)
            for s in range(m):
                if s!=t: D=D*(xs[T[t]]-xs[T[s]])
            Ds.append(D)
        # DD as single fraction with common denom prod(Ds): numerator = Σ_t f_t * ∏_{u≠t}D_u
        prodD=cyc_one(h)
        for D in Ds: prodD=prodD*D
        def dd_num(fv):
            tot=Cyc(h)
            for t in range(m):
                term=fv[T[t]]
                for u in range(m):
                    if u!=t: term=term*Ds[u]
                tot=tot+term
            return tot   # DD = tot / prodD
        Bnum=dd_num(xb)   # DD_T(x^b) numerator; denom prodD
        if Bnum.is_zero():
            continue       # denominator of γ is zero ⟹ ineligible
        eligible+=1
        Anum=dd_num(xa)
        # γ = -DD(x^a)/DD(x^b) = -(Anum/prodD)/(Bnum/prodD) = -Anum/Bnum.
        num=Cyc(h,[-v for v in Anum.c]); den=Bnum
        fracs.append((num,den))
    # dedup by cross-multiplication
    reps=[]
    for (num,den) in fracs:
        found=False
        for (rn,rd) in reps:
            if (num*rd - rn*den).is_zero():
                found=True; break
        if not found: reps.append((num,den))
    return len(reps), eligible

# ---------- modular (char-p) ----------
def isprime(x): return sympy.isprime(x)
def proot_n(p,n): return pow(sympy.primitive_root(p),(p-1)//n,p)

def DD_mod(Tidx,pts,fvals,p):
    s=0; m=len(Tidx)
    for t in range(m):
        den=1
        for u in range(m):
            if u!=t: den=(den*((pts[Tidx[t]]-pts[Tidx[u]])%p))%p
        s=(s+fvals[Tidx[t]]*pow(den,p-2,p))%p
    return s

def object_a_mod(p,n,k,a,b):
    z=proot_n(p,n); pts=[pow(z,i,p) for i in range(n)]
    pa=[pow(pt,a,p) for pt in pts]; pb=[pow(pt,b,p) for pt in pts]
    gammas=set(); eligible=0
    for T in itertools.combinations(range(n),k+1):
        db=DD_mod(T,pts,pb,p)
        if db%p==0: continue
        eligible+=1
        da=DD_mod(T,pts,pa,p)
        gammas.add(((-da)*pow(db,p-2,p))%p)
    return len(gammas),eligible

def solve_mod(M,rhs,p):
    m=len(M); A=[list(M[i])+[rhs[i]] for i in range(m)]; r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0: piv=i;break
        if piv is None: return None
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],p-2,p)
        A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c]; A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]

def object_b_mod(p,n,k,a,b):
    z=proot_n(p,n); pts=[pow(z,i,p) for i in range(n)]
    pa=[pow(pt,a,p) for pt in pts]; pb=[pow(pt,b,p) for pt in pts]
    ga={}
    for T in itertools.combinations(range(n),k+1):
        M=[]; rhs=[]
        for i in T:
            M.append([pow(pts[i],j,p) for j in range(k)]+[(-pa[i])%p]); rhs.append(pb[i]%p)
        sol=solve_mod(M,rhs,p)
        if sol is None: continue
        g=sol[:k]; gamma=sol[k]
        if gamma in ga: continue
        cnt=0
        for i in range(n):
            gi=0; xi=pts[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(pb[i]+gamma*pa[i])%p: cnt+=1
        ga[gamma]=cnt
    return {w:sum(1 for v in ga.values() if v>=w) for w in range(k+1,n+1)}

def main():
    print("="*78)
    print("Object (a) divided-difference bad-scalar count N ; Object (b) line-incidence I")
    print("char-0 = EXACT ℤ[ζ_n] ; char-p = mod q (q≡1 mod n)")
    print("="*78)
    cases=[(8,2,2,3),(8,2,2,4),(16,4,4,5),(16,4,5,7),(16,4,6,7)]
    for (n,k,a,b) in cases:
        print(f"\n### n={n} k={k} dir=({a},{b}) gcd(a-b,n)={math.gcd(a-b,n)}")
        N0,el0=object_a_exact(n,k,a,b)
        print(f"  (a) char-0 EXACT: N={N0}  eligible_T={el0}")
        primes=[p for p in range(n+1,80000) if (p-1)%n==0 and isprime(p)]
        thin=[p for p in primes if p<n*n][:3]
        thick=[p for p in primes if p>n**3][:3]
        sel=thin+thick
        viol=[]
        for p in sel:
            Np,elp=object_a_mod(p,n,k,a,b)
            reg="thin" if p<n*n else "thick"
            fl=""
            if Np>N0: fl="  <<< EXCEEDS char-0 (VIOLATES monotonicity)"; viol.append((p,Np))
            print(f"      (a) p={p:>6} ({reg:5},p/n^3={p/n**3:5.2f}): N={Np:>4} el={elp}{fl}")
        print(f"  (a) monotonicity N(char-p)<=N(char-0): {'HOLDS' if not viol else 'VIOLATED '+str(viol)}")
        print(f"  (b) line-incidence I(a,b,w):  char-0 ref = thickest prime")
        for p in sel:
            Iw=object_b_mod(p,n,k,a,b); reg="thin" if p<n*n else "thick"
            nz={w:Iw[w] for w in range(k+1,n+1) if Iw[w]}
            print(f"      (b) p={p:>6} ({reg:5}): bands {nz}")

if __name__=="__main__":
    main()
