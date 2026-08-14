#!/usr/bin/env python3
"""
DESIGNED-q over EXTENSION fields q = p^m  (#389 prize core).

Over a PRIME field q=p, the constraint n | p-1 forces p = 1 mod n, hence ord_n(p)=1:
p splits completely in Q(zeta_n).  The arithmetic of (p mod n) is then DEGENERATE.
The genuine "splitting of p in Q(zeta_n)" lever requires q = p^m with
   n | p^m - 1  but  n does NOT divide  p^d - 1  for d < m  (m = ord_n(p) = residue degree).
Then f = ord_n(p) = m is the order of Frobenius, and the cosets of mu_n in F_q^* fall
into Frobenius-orbits of size m (generically), giving  ~ k/m  distinct Gauss periods.

We build F_q = F_p[x]/(irreducible f of degree m), compute psi via the absolute trace
   psi(z) = exp(2 pi i Tr_{F_q/F_p}(z) / p),
and eta_b = sum_{y in mu_n} psi(b y), B = max_{b!=0}|eta_b|.

This is the TRUE designed-q setting.  We test the SEMIPRIMITIVE dichotomy:
  -1 in <p> mod n  <=>  Gauss periods are LARGE (~ sqrt(q));
  otherwise (generic Frobenius)  <=> are they ~ sqrt(n) (Ramanujan)?
And we ask: for n=2^mu fixed, is there an INFINITE family of (p,m) with B ~ sqrt(n)?

Implementation note: we work in GF(p^m) via a precomputed log/antilog table over a
chosen generator (Conway-free): find a primitive element by trying random elements.
Field elements are vectors in F_p^m; multiplication via the minimal polynomial.
For speed we use a discrete-log table once we have a generator g of F_q^*.
"""
import cmath, math, itertools, random
from collections import Counter

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f

def ord_mod(a,n):
    a%=n
    if math.gcd(a,n)!=1: return None
    o=1;x=a%n
    while x!=1: x=x*a%n; o+=1
    return o

# --- GF(p^m) arithmetic via an irreducible polynomial, represented as tuples ---
def poly_mulmod(a,b,modpoly,p):
    # a,b: lists of coeffs (low->high), len<=m ; modpoly: monic deg m as list len m+1
    m=len(modpoly)-1
    res=[0]*(2*m)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                res[i+j]=(res[i+j]+ai*bj)%p
    # reduce
    for i in range(len(res)-1,m-1,-1):
        c=res[i]
        if c:
            res[i]=0
            for j in range(m+1):
                res[i-m+j]=(res[i-m+j]-c*modpoly[j])%p
    return tuple(x%p for x in res[:m])

def find_irreducible(p,m):
    # find a monic irreducible polynomial of degree m over F_p, return as list len m+1 (low->high)
    # test irreducibility via: x^(p^m) = x mod f AND gcd-free of x^(p^d)-x for d|m proper.
    # We do a simple randomized search with the "x^{p^m}≡x and x^{p^{m/r}}≢ shares" Rabin test.
    facs=[m//r for r in factorize(m)]  # proper divisors m/prime
    def powmod_x(e, f):
        # compute x^e mod f (f monic list len m+1), return tuple len m
        result=tuple([1]+[0]*(m-1))  # 1
        base=tuple([0,1]+[0]*(m-2)) if m>=2 else tuple([0])
        # x is degree-1
        base=[0]*m; base[1%m]=1; base=tuple(base) if m>1 else (0,)
        # handle m==1 separately outside
        ee=e
        while ee>0:
            if ee&1: result=poly_mulmod(result,base,f,p)
            base=poly_mulmod(base,base,f,p)
            ee>>=1
        return result
    for _ in range(2000):
        # random monic poly
        f=[random.randrange(p) for _ in range(m)]+[1]
        if f[0]==0: continue
        # Rabin test
        # x^{p^m} == x ?
        xp_m=powmod_x(p**m, f)
        xident=[0]*m;
        if m>=2: xident[1]=1
        else: xident=[0]
        xident=tuple(xident)
        if m==1:
            return f  # any linear monic is irreducible
        if xp_m!=xident: continue
        ok=True
        for d in facs:
            xpd=powmod_x(p**d, f)
            # gcd(x^{p^d}-x, f) should be 1 -> for irreducibility x^{p^d}-x not div by f and shares no factor
            # simpler: x^{p^d} != x  (else f has factor of degree d| m)
            if xpd==xident: ok=False; break
        if ok: return f
    raise RuntimeError(f"no irreducible found p={p} m={m}")

def build_field(p,m):
    """Return (q, exp_table, log_table, mul, trace_fn) using a primitive element."""
    q=p**m
    f=find_irreducible(p,m)
    # element <-> int via base-p digits of the coeff tuple
    def to_int(t):
        x=0
        for c in reversed(t): x=x*p+(c%p)
        return x
    def to_tuple(x):
        d=[]
        for _ in range(m): d.append(x%p); x//=p
        return tuple(d)
    one=tuple([1]+[0]*(m-1))
    xelt=tuple([0,1]+[0]*(m-2)) if m>=2 else (0,)
    # find a generator g of F_q^* (primitive element): try candidates
    order=q-1
    pf=list(factorize(order).keys())
    def powt(a,e):
        r=one; b=a
        while e>0:
            if e&1: r=poly_mulmod(r,b,f,p)
            b=poly_mulmod(b,b,f,p); e>>=1
        return r
    g=None
    cand=[]
    # iterate over elements as integers 1..q-1 in a randomized order
    tries=list(range(1,min(q,200000)))
    random.shuffle(tries)
    for xi in tries:
        a=to_tuple(xi)
        if all(powt(a,order//pr)!=one for pr in pf):
            g=a; break
    if g is None: raise RuntimeError("no generator")
    # build log/antilog
    exp_t=[None]*(order)
    cur=one
    for i in range(order):
        exp_t[i]=cur
        cur=poly_mulmod(cur,g,f,p)
    log_t={}
    for i,e in enumerate(exp_t):
        log_t[e]=i
    # trace: Tr(z)= z + z^p + ... + z^{p^{m-1}}, an element of F_p (=its constant coeff as F_p)
    def trace(t):
        s=[0]*m
        cur=t
        for _ in range(m):
            for j in range(m): s[j]=(s[j]+cur[j])%p
            cur=powt(cur,p)  # Frobenius
        # s should be (tr,0,...,0): trace lies in F_p
        return s[0]%p
    return q, exp_t, log_t, f, one, g, trace, to_tuple

def gauss_B(p,m,n):
    """B = max_b |eta_b| over F_q=F_{p^m}, mu_n the n-th roots of unity."""
    q=p**m
    assert (q-1)%n==0, f"n={n} does not divide q-1={q-1}"
    q_,exp_t,log_t,f,one,g,trace,to_tuple=build_field(p,m)
    order=q-1
    k=order//n
    # mu_n = <g^k> : elements exp_t[k*j]
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p
    # eta_b depends only on coset of b: cosets repr by g^c, c=0..k-1
    # precompute trace of products
    absq=[]
    for c in range(k):
        bc=exp_t[c%order]
        s=0j
        for y in mu:
            prod=poly_mulmod(bc,y,f,p)
            s+=cmath.exp(1j*w*trace(prod))
        absq.append(abs(s)**2)
    B=math.sqrt(max(absq))
    return B, k, len(set(round(a,3) for a in absq)), absq

if __name__=="__main__":
    import sys
    random.seed(12345)
    n=int(sys.argv[1]) if len(sys.argv)>1 else 8
    print(f"### n={n}=2^{int(math.log2(n))}.  EXTENSION FIELDS q=p^m, n|q-1, vary ord_n(p)=m.")
    print(f"{'p':>5} {'m':>3} {'q=p^m':>10} {'f=ord_n(p)':>11} {'k':>8} {'#vals':>6} {'B':>9} {'B/sqrtn':>8} {'B/sqrtq':>8} {'semiprim':>9} {'gamma=ln n/ln q':>14}")
    # choose small primes p with n NOT dividing p-1 (so m>1 needed), and m = ord_n(p)
    results=[]
    for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]:
        if not is_prime(p): continue
        if p%n==1:
            m_needed=1
        else:
            m_needed=ord_mod(p,n)
        if m_needed is None: continue
        # use m = m_needed (the minimal extension where n|q-1)
        m=m_needed
        q=p**m
        if q>2_000_000: continue   # keep k feasible
        try:
            B,k,nv,absq=gauss_B(p,m,n)
        except Exception as e:
            print(f"  p={p} m={m}: ERR {e}"); continue
        f=ord_mod(p%n,n)
        # semiprimitive: -1 in <p mod n>
        sp=False; x=p%n
        for t in range(1,(f or 1)+1):
            if x==(n-1)%n: sp=True; break
            x=x*(p%n)%n
        gamma=math.log(n)/math.log(q)
        results.append((p,m,q,f,k,nv,B,sp,gamma))
        print(f"{p:>5} {m:>3} {q:>10} {str(f):>11} {k:>8} {nv:>6} {B:>9.3f} "
              f"{B/math.sqrt(n):>8.3f} {B/math.sqrt(q):>8.3f} {str(sp):>9} {gamma:>14.3f}")
    print("\n### grouped by semiprimitive:")
    for sp in (False,True):
        v=[r for r in results if r[7]==sp]
        if v:
            ratios=[r[6]/math.sqrt(n) for r in v]
            rq=[r[6]/math.sqrt(r[2]) for r in v]
            print(f"  semiprim={sp}: count={len(v)}  B/sqrtn min={min(ratios):.3f} max={max(ratios):.3f}"
                  f"  B/sqrtq min={min(rq):.3f} max={max(rq):.3f}")
    print("\n### grouped by f=ord_n(p):")
    byf={}
    for r in results: byf.setdefault(r[3],[]).append(r[6]/math.sqrt(n))
    for f in sorted(byf, key=lambda x:(x is None,x)):
        v=byf[f]; print(f"  f={f}: count={len(v)} B/sqrtn min={min(v):.3f} mean={sum(v)/len(v):.3f} max={max(v):.3f}")
