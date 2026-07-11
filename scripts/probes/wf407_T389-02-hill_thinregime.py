#!/usr/bin/env python3
"""
wf407 / T389-02-hill : THIN PRIZE REGIME (p ~ n^4) far-line incidence extremizer.

We use the EXACT bad-scalar census (no per-gamma list-decode sweep -> works at huge p):

For a 2-row monomial stack with DIRECTION u1=X^a and OFFSET u0=X^b on mu_n, agreement
threshold w, a scalar gamma is BAD iff there is a w-subset S of mu_n and a degree-<k poly P
with  P(x) = x^b + gamma*x^a  for all x in S.

Fix S (|S|=w).  The map x -> (x^b + gamma*x^a) must equal a deg-<k poly on S.  A function on
the w points of S equals a deg-<k poly iff its (w-k) top finite-differences (Lagrange residuals)
vanish.  Linear in gamma:  residual_j(S) = A_j(S) + gamma*B_j(S) = 0  for j=1..w-k, where
A_j = residual of x^b, B_j = residual of x^a.  So per S there is at most ONE bad gamma
(= -A_1/B_1) consistent across all residuals.  We collect the set of such gamma over all S.

I(dir(a,b)) = |{ bad gamma over all w-subsets S }|.

This is the q-independent symmetric-function census of the workbench R4 route, made fully exact.
Runs at p = 65537 (Fermat, the n=16 thin regime p>n^4) and at toy primes for cross-check.
"""
import itertools, sys

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primitive_root(p):
    fs=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0: fs.add(d);m//=d
        d+=1
    if m>1: fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def mu_n(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def deg_lt_k_residual_coeffs(xs, vals_a, vals_b, k, p):
    """For points xs (|S|=w), and two value-vectors (x^a, x^b on S), determine the bad gamma
       (if any) s.t. vals_b + gamma*vals_a is a deg-<k poly on xs.
       Method: divided differences. f equals deg<k poly on w points iff all divided differences
       of order >= k vanish. f = vb + g*va, linear in g. Solve dd_k = 0 (and check higher).
       Returns gamma (int in F_p) or None.
    """
    w=len(xs)
    # divided differences table for a generic value vector v -> list of leading dd of orders k..w-1
    def dd_orders(v):
        # full divided difference triangle; return dd of order j (j from 0..w-1) as v[0..]
        tab=[list(v)]
        cur=list(v)
        for order in range(1,w):
            nxt=[]
            for i in range(w-order):
                num=(cur[i+1]-cur[i])%p
                den=(xs[i+order]-xs[i])%p
                nxt.append((num*pow(den,p-2,p))%p)
            tab.append(nxt)
            cur=nxt
        # dd of order j is tab[j][0]
        return [tab[j][0] for j in range(w)]
    da=dd_orders(vals_a)   # divided differences of x^a vector
    db=dd_orders(vals_b)
    # need: for all orders j in [k, w-1]:  db[j] + gamma*da[j] = 0
    gamma=None
    for j in range(k, w):
        Aj=db[j]; Bj=da[j]
        if Bj%p==0:
            if Aj%p!=0:
                return None  # 0 = nonzero, no gamma
            # else any gamma ok for this order
        else:
            gj=(-Aj*pow(Bj,p-2,p))%p
            if gamma is None: gamma=gj
            elif gamma!=gj: return None
    return gamma  # may be None only if all orders had Bj=0 & Aj=0 (then every gamma works -> saturates)

def census_incidence(dom, a, b, k, w, p):
    """Exact bad-gamma count for dir(a,b) over all w-subsets. Returns (count, saturated_flag)."""
    n=len(dom)
    bad=set()
    saturate=False
    va_full=[pow(x,a,p) for x in dom]
    vb_full=[pow(x,b,p) for x in dom]
    for S in itertools.combinations(range(n), w):
        xs=[dom[i] for i in S]
        va=[va_full[i] for i in S]; vb=[vb_full[i] for i in S]
        g=deg_lt_k_residual_coeffs(xs, va, vb, k, p)
        if g is None:
            # either no gamma OR all-orders-free (saturate). Distinguish:
            # recompute: if for ALL j in [k,w): da[j]=0 and db[j]=0 -> any gamma works
            # cheap re-test:
            if _all_free(xs, va, vb, k, w, p):
                saturate=True
        else:
            bad.add(g)
    return len(bad), saturate

def _all_free(xs, va, vb, k, w, p):
    def dd(v):
        cur=list(v); res=[]
        out=[v[0]]
        for order in range(1,w):
            nxt=[]
            for i in range(w-order):
                nxt.append(((cur[i+1]-cur[i])*pow((xs[i+order]-xs[i])%p,p-2,p))%p)
            out.append(nxt[0]); cur=nxt
        return out
    da=dd(va); db=dd(vb)
    return all(da[j]%p==0 and db[j]%p==0 for j in range(k,w))

def run(n,k,p,w,amax=None,label=""):
    print(f"\n===== {label}: n={n} k={k} p={p} w={w} (rho={k/n:.3f}; n^4={n**4}, p>n^4: {p>n**4}) =====",flush=True)
    dom=mu_n(p,n)
    amax = amax if amax else n-1
    rows=[]
    for a in range(k, amax+1):
        for b in range(0, a):
            cnt,sat=census_incidence(dom,a,b,k,w,p)
            tag="SAT" if sat else ""
            rows.append((a,b,cnt,tag))
    rows.sort(key=lambda r:-r[2])
    print(" top dir(a,b) by census incidence:",flush=True)
    for a,b,c,tag in rows[:10]:
        adj="ADJ" if a-b==1 else f"gap{a-b}"
        print(f"   dir(a={a:2d},b={b:2d}) I={c:4d}  [{adj}] {tag}",flush=True)
    bb=rows[0]
    print(f" => BEST dir(a={bb[0]},b={bb[1]}) I={bb[2]}  [{'ADJ' if bb[0]-bb[1]==1 else 'gap'+str(bb[0]-bb[1])}]",flush=True)
    # low-vs-high tabulation: best incidence per direction-exponent a
    bya={}
    for a,b,c,tag in rows:
        bya[a]=max(bya.get(a,-1),c)
    print(" best incidence per direction-exponent a (LOW->HIGH):",flush=True)
    for a in sorted(bya):
        print(f"   a={a:2d}: maxI={bya[a]}",flush=True)
    return bb

if __name__=="__main__":
    # cross-check at toy prime first (should match v3): (12,6) w=9 -> (X^9,X^8)=12
    run(12,6,13,9,label="XCHK toy (12,6) p=13")
    # THIN PRIZE REGIME n=16, p=65537 (Fermat >16^4=65536), agreement w=9 (deep band, past Johnson)
    run(16,8,65537,9,label="THIN (16,8) p=65537 w=9")
    # also w=10 (one notch toward capacity) and w=11
    run(16,8,65537,10,label="THIN (16,8) p=65537 w=10")
    # n=32 thin regime: p>32^4=1048576; smallest prime ==1 mod 32 above that.
    # find it:
    pp=1048576+1
    while not (pp%32==1 and is_prime(pp)): pp+=1
    # (32, k=16) w too large for C(32,w); use modest deep band w=18 (still C(32,18)=471435600 too big!)
    # -> n=32 full census is infeasible; SKIP exact, note in KB. Instead do n=20 thin as a bridge.
    n=20;p20=20**4+1
    while not (p20%20==1 and is_prime(p20)): p20+=1
    print(f"\n(n=20 thin prime p={p20}; C(20,11)={ __import__('math').comb(20,11)})",flush=True)
    run(20,10,p20,11,amax=15,label="THIN (20,10) deep band w=11")
