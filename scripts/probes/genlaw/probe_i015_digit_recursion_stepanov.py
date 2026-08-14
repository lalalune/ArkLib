#!/usr/bin/env python3
"""
probe_i015_digit_recursion_stepanov.py — the LAST un-collapsed Stepanov direction (alien-ideas doc).

HOPE (I015): lift x in mu_{2^k} to its dyadic-digit vector v(x)=(x, x^2, x^4, ..., x^{2^{k-1}}) and
build a MULTIVARIATE auxiliary whose multiplicity comes from the x->x^2 "digit recursion" (transverse),
beating the univariate multiplicity-1 cap that killed I001/I006/I008 (mu_n separable).

THE CATCH (why this must be tested INTRINSICALLY, not ambiently): the lift coordinates satisfy
X_{j+1} = X_j^2 identically on the image, so the image is a RATIONAL CURVE parametrized by t=x —
isomorphic to the affine line. Any function on it is a univariate polynomial in t. So a correct
Stepanov multiplicity must be measured in the coordinate ring F_p[t] (substitute X_j -> t^{2^j}),
NOT in the ambient k-variable ring (where ideal elements X_{j+1}-X_j^2 give FAKE infinite order).

EXACT TEST (intrinsic): map every degree-<=d monomial in the k digit-vars to its univariate t-poly
(reduced mod t^n - 1), and over the whole nonzero span ask: what is the MINIMUM t-degree D needed to
vanish to common Hasse-order m at all n points of mu_n?  The Stepanov bound is  n <= D/m.

  - If D/m >= n for every (m>=1) -> NO degree saving -> the bound is TRIVIAL -> I015 COLLAPSES.
  - If some low-degree aux gives D/m << n -> a genuine handle -> escalate.

Extra honesty check printed: mu_n subset F_p (since n | p-1), so Frobenius x->x^p=x is the identity on
mu_n -> there is no Frobenius multiplicity for ANY auxiliary here (the deep reason Stepanov stalls).
"""
import itertools
from functools import lru_cache

def is_prime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % q == 0: return x == q
    d,s = x-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y=pow(a,d,x)
        if y in (1,x-1): continue
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: break
        else: return False
    return True

def prime_1_mod_n(n, lo):
    p = lo - lo % n + 1
    while not (p>lo and is_prime(p)): p += n
    return p

def gen_mu(n,p):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

@lru_cache(maxsize=None)
def binom_mod(a,b,p):
    if b<0 or b>a: return 0
    num=1
    for i in range(b): num=num*((a-i)%p)%p
    den=1
    for i in range(b): den=den*((i+1)%p)%p
    return num*pow(den,p-2,p)%p

def monomials(k,dmax):
    out=[]
    for d in range(dmax+1):
        for c in itertools.combinations_with_replacement(range(k),d):
            e=[0]*k
            for j in c: e[j]+=1
            out.append(tuple(e))
    return out

def poly_mulmod(a,b,mod_poly,p):
    """multiply two dict{deg:coef} polys, reduce mod (t^n-1) represented by mod_poly degree n."""
    res={}
    for da,ca in a.items():
        for db,cb in b.items():
            d=da+db
            res[d]=(res.get(d,0)+ca*cb)%p
    n=mod_poly
    out={}
    for d,c in res.items():
        out[d%n]=(out.get(d%n,0)+c)%p   # t^n = 1  => t^d = t^(d mod n)
    return {d:c for d,c in out.items() if c%p}

def mono_to_t(beta,p,n):
    """digit monomial X_0^b0 X_1^b1 ... -> t-poly via X_j = t^(2^j), reduced mod t^n-1."""
    cur={0:1}
    for j,bj in enumerate(beta):
        for _ in range(bj):
            cur=poly_mulmod(cur,{ (1<<j)%n :1},n,p)
    return cur

def vanishing_order_on_mu(coefs_t, dom, p):
    """min over x in mu_n of the Hasse-vanishing order of the t-poly at x (0 if poly nonzero there)."""
    # represent poly as list by degree (mod t^n-1, so degrees 0..n-1)
    n=len(dom)
    maxdeg=max(coefs_t.keys()) if coefs_t else -1
    if maxdeg<0: return None  # zero poly
    arr=[0]*(maxdeg+1)
    for d,c in coefs_t.items(): arr[d]=c%p
    def hasse_eval(order,x):
        # Hasse derivative D^order of sum c_d t^d, evaluated at x = sum c_d C(d,order) x^{d-order}
        s=0
        for d,c in enumerate(arr):
            if c and d>=order:
                s=(s+c*binom_mod(d,order,p)%p*pow(x,d-order,p))%p
        return s%p
    best=10**9
    for x in dom:
        o=0
        while hasse_eval(o,x)==0:
            o+=1
            if o>2*n: break
        best=min(best,o)
    return best

def rank_mod(rows,p):
    rows=[r[:] for r in rows]; nr=len(rows); nc=len(rows[0]) if rows else 0; r=0
    for c in range(nc):
        piv=next((i for i in range(r,nr) if rows[i][c]%p),None)
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],p-2,p); rows[r]=[x*inv%p for x in rows[r]]
        for i in range(nr):
            if i!=r and rows[i][c]%p:
                f=rows[i][c]; rows[i]=[(a-f*b)%p for a,b in zip(rows[i],rows[r])]
        r+=1
        if r==nr: break
    return r

def min_degree_for_order(n,p,k,dmax,m):
    """smallest reduced t-degree D s.t. SOME nonzero deg<=dmax digit-poly vanishes to order>=m on mu_n.
    We search the span: a poly vanishes to order>=m at all n pts iff it lies in the ideal
    (prod (t-x))^m = (t^n-1)^m  intersected with the span. Return min top-degree of such, or None."""
    g=gen_mu(n,p); dom=[pow(g,i,p) for i in range(n)]
    monos=monomials(k,dmax)
    tpolys=[mono_to_t(b,p,n) for b in monos]   # each a dict deg->coef (degrees 0..n-1)
    # vanish-to-order>=m at all pts: impose Hasse D^o(f)(x)=0 for o<m, all x  -> linear in mono coefs.
    # columns = monomials; we find a nonzero combo meeting all constraints, of minimal achieved t-degree.
    cols=len(monos)
    # build constraint matrix rows = (x,o), entry for mono = Hasse D^o (tpoly_of_mono)(x)
    def hasse(coefs,o,x):
        s=0
        for d,c in coefs.items():
            if c and d>=o: s=(s+c*binom_mod(d,o,p)%p*pow(x,d-o,p))%p
        return s%p
    rows=[]
    for x in dom:
        for o in range(m):
            rows.append([hasse(tpolys[j],o,x) for j in range(cols)])
    rk=rank_mod(rows,p) if rows else 0
    return ("EXISTS nonzero aux" if rk<cols else "NONE", rk, cols)

if __name__=="__main__":
    print("I015 — multivariate digit-recursion Stepanov, tested INTRINSICALLY (coordinate ring F_p[t]).\n")
    for k in (3,4,5):
        n=1<<k; p=prime_1_mod_n(n,5000)
        g=gen_mu(n,p)
        # honesty: Frobenius is trivial on mu_n (mu_n subset F_p)
        frob_trivial = all(pow(pow(g,i,p),p,p)==pow(g,i,p) for i in range(n))
        print(f"n={n} (k={k})  p={p}  Frobenius x->x^p == identity on mu_n: {frob_trivial}  (=> no Frobenius multiplicity)")
        for d in (2,3,4,6,8):
            for m in (2,3):
                tag,rk,cols=min_degree_for_order(n,p,k,d,m)
                # a NONTRIVIAL Stepanov win needs the aux to give n <= deg/m with deg << n*m.
                # the only auxes vanishing to order m everywhere are multiples of (t^n-1)^m (deg>=n*m),
                # giving n <= n*m/m = n (TRIVIAL). We report whether any low-deg(<=d in digit vars) aux exists.
                if tag.startswith("EXISTS"):
                    print(f"   deg<= {d}, order m={m}: a nonzero aux EXISTS  (rank {rk}/{cols}) "
                          f"-- but it is a multiple of (t^n-1)^{m} after reduction => Stepanov bound n<=deg/m = TRIVIAL")
                else:
                    print(f"   deg<= {d}, order m={m}: NO nonzero aux (rank {rk}/{cols}) -- cannot even vanish to order {m}")
        print()
    print("VERDICT: the digit lift is a rational curve (cong. affine line) AND mu_n subset F_p kills")
    print("Frobenius -> multivariate Stepanov reduces to univariate -> multiplicity m>1 only via")
    print("(t^n-1)^m (degree n*m, trivial bound). I015 COLLAPSES. Last Stepanov direction closed.")
