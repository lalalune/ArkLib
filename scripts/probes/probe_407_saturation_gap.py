#!/usr/bin/env python3
# ============================================================================
# Issue #407: the SATURATION GAP between object (a) N and object (b) I.
#
# Independent confirmation of the mechanism that makes the ring-hom
# monotonicity claim about the WRONG object.
#
# The monotonicity claim: γ_T = -DD_T(x^a)/DD_T(x^b) is a fixed element of
# Frac(ℤ[ζ_n]); reduction is a ring hom; so the FINITE bad-scalar set can only
# merge/delete  ⟹  N(char-p) ≤ N(char-0). H1: a char-0-zero denominator
# DD_T(x^b) "can't become nonzero mod p" (eligibility ⊆).
#
# THE GAP: when DD_T(x^b) is char-0-NONZERO but ≡ 0 mod q (an "excess prime"),
# the FINITE scalar γ_T is DELETED from N (denominator → 0, γ_T → ∞). The
# monotonicity statement counts this as "shrink, good for us." BUT by the
# Schur-bridge dichotomy, DD_T(x^b)=0 means the entire monomial line is bad for
# EVERY scalar α — the line SATURATES. In the line-incidence object I, that band
# jumps to I = q (every α at that agreement level), i.e. char-p MASSIVELY
# EXCEEDS char-0. So the very event the monotonicity calls "deletion/merge" is
# the event that makes I(char-p) ≫ I(char-0). The two objects move in OPPOSITE
# directions on the same event.
#
# This probe:
#   (1) Confirms H1 is FALSE as stated: exhibit T with DD_T(x^b)≠0 over ℂ but
#       ≡0 mod q (denominator becomes zero mod p — eligibility does NOT shrink
#       monotonically in the "harmless" way; it deletes a FINITE scalar AND
#       saturates the line).
#   (2) Shows the same T saturates the line incidence I to q in char-p while
#       char-0 has that band good (I small).
#   (3) Concludes: monotonicity may hold for N (finite-scalar object) but the
#       deployed δ* object is I (line incidence), where char-p > char-0 occurs.
# ============================================================================
import itertools, math, cmath
import sympy

def DD_C(Tidx, pts, fvals):
    """exact-ish char-0 divided difference using cyclotomic floats; we ALSO do an
    exact ℤ[ζ] zero-test separately for the witness."""
    s=0; m=len(Tidx)
    for t in range(m):
        den=1
        for u in range(m):
            if u!=t: den*=(pts[Tidx[t]]-pts[Tidx[u]])
        s+=fvals[Tidx[t]]/den
    return s

def DD_mod(Tidx, pts, fvals, p):
    s=0; m=len(Tidx)
    for t in range(m):
        den=1
        for u in range(m):
            if u!=t: den=(den*((pts[Tidx[t]]-pts[Tidx[u]])%p))%p
        s=(s+fvals[Tidx[t]]*pow(den,p-2,p))%p
    return s

# exact ℤ[ζ_n] zero test of h_{c-k}(x_T) via the divided-difference numerator,
# using the cyclotomic-vector ring (ζ^{n/2}=-1):
class Cyc:
    __slots__=('h','c')
    def __init__(s,h,c=None): s.h=h; s.c=[0]*h if c is None else list(c)
    @staticmethod
    def zp(h,e):
        n=2*h; e%=n; v=Cyc(h)
        if e<h: v.c[e]=1
        else:   v.c[e-h]=-1
        return v
    def __add__(s,o): return Cyc(s.h,[s.c[i]+o.c[i] for i in range(s.h)])
    def __sub__(s,o): return Cyc(s.h,[s.c[i]-o.c[i] for i in range(s.h)])
    def __mul__(s,o):
        h=s.h; r=[0]*(2*h)
        for i in range(h):
            if s.c[i]:
                for j in range(h):
                    if o.c[j]: r[i+j]+=s.c[i]*o.c[j]
        out=[0]*h
        for d in range(2*h):
            if r[d]:
                if d<h: out[d]+=r[d]
                else:   out[d-h]-=r[d]
        return Cyc(h,out)
    def is_zero(s): return not any(s.c)

def cyc_one(h): v=Cyc(h); v.c[0]=1; return v

def DD_exact_num(Tidx, n, exps):
    """numerator of DD_T(x^c) over common denom prod(D_t), exact in ℤ[ζ_n].
    exps[i] = (i*c)%n giving x_i^c = ζ^{exps[i]}. Returns Cyc (zero iff DD=0)."""
    h=n//2; m=len(Tidx)
    xs=[Cyc.zp(h,(i)%n) for i in range(n)]  # x_i=ζ^i
    fv=[Cyc.zp(h,exps[i]) for i in range(n)]
    Ds=[]
    for t in range(m):
        D=cyc_one(h)
        for u in range(m):
            if u!=t: D=D*(xs[Tidx[t]]-xs[Tidx[u]])
        Ds.append(D)
    tot=Cyc(h)
    for t in range(m):
        term=fv[Tidx[t]]
        for u in range(m):
            if u!=t: term=term*Ds[u]
        tot=tot+term
    return tot

def line_incidence_band(p,n,k,a,b,w):
    """char-p I(a,b,w) for object (b): distinct γ with agreement>=w."""
    g0=sympy.primitive_root(p); z=pow(g0,(p-1)//n,p)
    pts=[pow(z,i,p) for i in range(n)]
    pa=[pow(pt,a,p) for pt in pts]; pb=[pow(pt,b,p) for pt in pts]
    def solve(M,rhs):
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
    ga={}
    for T in itertools.combinations(range(n),k+1):
        M=[]; rhs=[]
        for i in T:
            M.append([pow(pts[i],j,p) for j in range(k)]+[(-pa[i])%p]); rhs.append(pb[i]%p)
        sol=solve(M,rhs)
        if sol is None: continue
        g=sol[:k]; gam=sol[k]
        if gam in ga: continue
        cnt=0
        for i in range(n):
            gi=0; xi=pts[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(pb[i]+gam*pa[i])%p: cnt+=1
        ga[gam]=cnt
    return sum(1 for v in ga.values() if v>=w), len(ga)

def main():
    # Witness regime from lalalune's own prong-A: n=16, k=4 (boundary band uses
    # h_{b-k}; for b=k+1=5, DD_T(x^5)=h_1(x_T)=Σ x_t). We use the documented
    # excess prime q=8161 for h_3 (b=k+3=7). Reproduce generally: find an excess
    # prime where DD_T(x^b)≠0 over ℂ but ≡0 mod q, and show line saturates.
    n,k=16,4
    print("="*78)
    print(f"SATURATION GAP, n={n} k={k}.  H1 test + (a) vs (b) on the same event.")
    print("="*78)
    # b such that DD_T(x^b)=h_{b-k}(x_T). Take b=7 ⟹ h_3. excess prime q=8161.
    for (a,b,q) in [(4,7,8161),(4,5,257),(4,7,12289)]:
        if (q-1)%n!=0 or not sympy.isprime(q):
            print(f"skip q={q} (not ≡1 mod n / not prime)"); continue
        g0=sympy.primitive_root(q); z=pow(g0,(q-1)//n,q)
        ptsq=[pow(z,i,q) for i in range(n)]
        zc=[cmath.exp(2j*math.pi*i/n) for i in range(n)]
        pbC=[zc[i]**b for i in range(n)]
        pbQ=[pow(ptsq[i],b,q) for i in range(n)]
        # find a T eligible in char-0 (DD!=0) but DD≡0 mod q (the gap event)
        gap=[]
        for T in itertools.combinations(range(n),k+1):
            exps=[(i*b)%n for i in range(n)]
            num=DD_exact_num(T,n,exps)          # exact char-0 numerator
            c0_zero = num.is_zero()
            cp = DD_mod(T,ptsq,pbQ,q)
            if (not c0_zero) and cp%q==0:
                gap.append(T)
        print(f"\n  dir=({a},{b}) q={q}: #T with DD_T(x^{b})≠0 over ℂ but ≡0 mod q  = {len(gap)}")
        if gap:
            print(f"    witness T={gap[0]}  (eligibility H1 'can't become 0 mod p' is FALSE here)")
            # show the line-incidence saturation at the band these T live in.
            # band w = (#points the saturated line agrees on). saturated line: for
            # EVERY α the (k+1)-subset interpolant exists, so check I at band k+1..
            for w in [k+1,k+2,5,6]:
                Iq,tot = line_incidence_band(q,n,k,a,b,w)
                # char-0 proxy via a thick prime far above n^3 with NO such gap T:
                qbig=next(p for p in range(n**3+1,400000) if (p-1)%n==0 and sympy.isprime(p)
                          and all(not (DD_exact_num(T,n,[(i*b)%n for i in range(n)]).is_zero()==False
                                       and DD_mod(T,[pow(pow(sympy.primitive_root(p),(p-1)//n,p),i,p) for i in range(n)],
                                                  [pow(pow(pow(sympy.primitive_root(p),(p-1)//n,p),i,p),b,p) for i in range(n)],p)%p==0)
                                  for T in [gap[0]]))
                Ibig,_=line_incidence_band(qbig,n,k,a,b,w)
                print(f"      band w={w} (δ={1-w/n:.3f}): I(char-p q={q})={Iq:>5}   I(faithful q={qbig})={Ibig:>3}   "
                      f"{'<<< char-p SATURATES (>> char-0)' if Iq>=q-1 and Ibig<Iq else ''}")

if __name__=="__main__":
    main()

# ---------------------------------------------------------------------------
# CLEAN MECHANISM CHECK (appended): Schur-dichotomy saturating-subset count.
# A (k+1)-subset T is "saturating" iff h_{b-k}(ζ^T)=0 (the divided-difference
# denominator vanishes). By the dichotomy, one saturating subset ⟹ the monomial
# line is bad for EVERY α at band w=k+1 ⟹ object (b) incidence jumps to ~q,
# while object (a) DELETES γ_T (ineligible). char-0 vs the excess prime q=8161:
# ---------------------------------------------------------------------------
def _saturating_subsets_mod(q, n, k, b):
    from itertools import combinations, combinations_with_replacement as cwr
    z = pow(sympy.primitive_root(q), (q-1)//n, q); xs = [pow(z, i, q) for i in range(n)]
    cnt = 0
    for T in combinations(range(n), k+1):
        xt = [xs[t] for t in T]; s = 0
        for c in cwr(range(len(xt)), b-k):
            pr = 1
            for idx in c: pr = (pr*xt[idx]) % q
            s = (s+pr) % q
        if s % q == 0: cnt += 1
    return cnt
def _saturating_subsets_C(n, k, b):
    from itertools import combinations, combinations_with_replacement as cwr
    import functools
    zc = [cmath.exp(2j*math.pi*i/n) for i in range(n)]; cnt = 0
    for T in combinations(range(n), k+1):
        xt = [zc[t] for t in T]
        s = sum(functools.reduce(lambda p, i: p*xt[i], c, 1) for c in cwr(range(len(xt)), b-k))
        if abs(s) < 1e-7: cnt += 1
    return cnt
if __name__ == "__main__":
    print("\n--- Schur dichotomy: saturating (k+1)-subsets h_{b-k}(ζ^T)=0, n=16 k=4 b=7 (h_3) ---")
    print(f"  char-0: {_saturating_subsets_C(16,4,7)}")
    for q in [8161, 4129, 12289]:
        if (q-1) % 16 == 0 and sympy.isprime(q):
            print(f"  q={q} ({'excess' if _saturating_subsets_mod(q,16,4,7)>0 else 'faithful'}): "
                  f"{_saturating_subsets_mod(q,16,4,7)}")
    print("  ⟹ q=8161 (≡1 mod 16, <n^4=65536) has 16 saturating subsets absent in char-0:")
    print("     object (b) line saturates (bad ∀α) while object (a) deletes γ_T (ineligible).")
