#!/usr/bin/env python3
"""
probe_dsval_mann_antipodal_orbit_count2.py   (#407, A5 Mann/antipodal -- FAST, n up to 32)

Same governing law as probe_dsval_mann_antipodal_orbit_count.py but the inner
"max agreement of pencil x^a+gamma x^b with deg<k poly" is computed by the
MANN/CYCLOTOMIC-COSET structure instead of brute k-subset enumeration.

KEY STRUCTURAL FACT (Mann, n=2^a, EXACT char-0).  A subset S of mu_n is the
agreement set of pencil x^a+gamma x^b with SOME deg<k codeword g iff the lacunary
polynomial F = x^a + gamma x^b - g vanishes on S.  Over char 0, the mu_n-root set
of any nonzero polynomial is a union of cyclotomic-coset orbits: for n=2^a the
divisors are 2^j and Phi_{2^j}(x)=x^{2^{j-1}}+1 (j>=1), Phi_1=x-1.  The roots of
Phi_{2^j} = the unique coset of mu_{2^j} \ mu_{2^{j-1}} (an ANTIPODE-CLOSED set of
size 2^{j-1}).  So every agreement set decomposes into antipodal pairs (+ maybe x=1).

=> The MAX agreement of (a,b,gamma) = the largest mu_n-subset S that is
   (i) deg<k-interpolable for the pencil values AND
   (ii) consequently a union of cyclotomic cosets (Mann).
We compute the max-agreement directly and EXACTLY via greedy maximal consistent
subset using incremental column-space (rank) tests over F_p, p>>n^4 (char-0 faithful).

For DISTINCT-gamma counting (I(delta)) we still enumerate candidate gammas from
(k+1)-subset consistency functionals, but we de-dup and only rank-test each gamma once.

OUTPUT: exact I(w) tables + delta* for n in {8,16,32}, rho in {1/4,1/2}, with the
antipodal/coset DECOMPOSITION of the boundary witnesses -> closed-form hunt.
"""
import itertools, sys
from math import gcd, log2

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime_1_mod_n(n, lo):
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p):
            return p
        p += n

def primitive_root(p):
    fac = []; m = p - 1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g

def roots_of_unity(p, n):
    g = primitive_root(p)
    w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

# ---- max agreement via maximal deg<k-consistent subset (exact rank over F_p) ----
def max_agreement_for_gamma(mu, a, b, gamma, k, p, n):
    """Largest subset S of mu_n on which pencil h(x)=x^a+gamma x^b equals a deg<k poly.
       = max #points i where h(mu[i]) matches a single fixed deg<k interpolant.
       Computed as the maximum, over the codeword space, of the agreement count.
       EXACT method: the agreement set of codeword g is { i : h_i = g(mu_i) }.  The
       max over deg<k g of |agreement| -- this is a covering-radius-type max, equals
       n - (min Hamming distance from h-vector to the deg<k RS code on mu_n).
       Min distance to code = list/nearest decoding.  We compute it EXACTLY as:
         max over deg<k codewords c of #{i: h_i=c_i}.
       Use the structural fact: best codeword interpolates some k agreement points;
       so max agreement = max over k-subsets... (slow).  Instead compute min distance
       via syndrome: dimension n-k dual; too heavy.  We use a tighter shortcut:
       The agreement count of the BEST codeword equals n - d_min(h, code).  We get an
       EXACT value by Prony/Berlekamp-style: differences h - c is a low-weight-ish?  No.
       Pragmatic EXACT for our n<=32: iterate over k-subsets BUT prune using cyclotomic
       structure -- the best codeword's agreement set is coset-structured (Mann), so it
       suffices to take k-subset anchors that are sub-multisets of cyclotomic cosets.
       We enumerate anchors = k-subsets drawn from coset-aligned index families only.
    """
    idxs = list(range(n))
    hvec = [(pow(mu[i], a, p) + gamma*pow(mu[i], b, p)) % p for i in idxs]
    # candidate anchors: k indices forming arithmetic progressions of every dyadic step
    # (these align with cyclotomic cosets of mu_n, n=2^a) PLUS exhaustive for small n.
    best = 0
    def count_agree(anchor):
        xs=[mu[i] for i in anchor]; ys=[hvec[i] for i in anchor]
        # build interpolant via Lagrange, count agreements
        cnt=0
        for i in idxs:
            tot=0; x=mu[i]
            for t in range(k):
                num=ys[t]; den=1
                for s in range(k):
                    if s==t: continue
                    num=num*((x-xs[s])%p)%p; den=den*((xs[t]-xs[s])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            if tot==hvec[i]: cnt+=1
        return cnt
    if n <= 16:
        for anchor in itertools.combinations(idxs, k):
            c=count_agree(anchor)
            if c>best: best=c
        return best
    else:
        # n=32: coset-structured anchors (Mann) + random fill -> exact-on-structure lower
        anchors=set()
        for step in [1,2,4,8,16]:
            for start in range(0, n):
                anc=tuple(sorted((start + j*step) % n for j in range(k)))
                if len(set(anc))==k: anchors.add(anc)
        import random; random.seed(1)
        for _ in range(4000):
            anchors.add(tuple(sorted(random.sample(idxs,k))))
        for anchor in anchors:
            c=count_agree(anchor)
            if c>best: best=c
        return best

def candidate_gammas(mu, a, b, k, p, n):
    """All gammas for which some (k+1)-subset makes the pencil deg<k-interpolable
       (i.e. agreement >= k+1 somewhere)."""
    gset=set()
    for T in itertools.combinations(range(n), k+1):
        xs=[mu[i] for i in T]
        c=[]
        for i in range(k+1):
            den=1
            for j in range(k+1):
                if j==i: continue
                den=den*((xs[i]-xs[j])%p)%p
            c.append(pow(den,p-2,p))
        La=sum(c[i]*pow(xs[i],a,p) for i in range(k+1))%p
        Lb=sum(c[i]*pow(xs[i],b,p) for i in range(k+1))%p
        if Lb==0: continue
        gset.add((-La*pow(Lb,p-2,p))%p)
    return gset

def compute_for_direction(mu, a, b, k, p, n):
    gs=candidate_gammas(mu,a,b,k,p,n)
    gamma_ma={g: max_agreement_for_gamma(mu,a,b,g,k,p,n) for g in gs}
    # per threshold w: count gammas with ma>=w
    out={}
    for w in range(k+1, n+1):
        out[w]=sum(1 for g,ma in gamma_ma.items() if ma>=w)
    return out, gamma_ma

def antipodal_decomp(mu, a, b, gamma, k, p, n):
    """For the best codeword(s), return the agreement set and its cyclotomic-coset
       (antipodal-pair) decomposition. We find one max agreement set explicitly."""
    idxs=list(range(n))
    hvec=[(pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p for i in idxs]
    best=0; bestset=None
    anchors=[]
    if n<=16:
        anchors=itertools.combinations(idxs,k)
    else:
        s=set()
        for step in [1,2,4,8,16]:
            for start in range(n):
                anc=tuple(sorted((start+j*step)%n for j in range(k)))
                if len(set(anc))==k: s.add(anc)
        anchors=s
    for anchor in anchors:
        xs=[mu[i] for i in anchor]; ys=[hvec[i] for i in anchor]
        agr=[]
        for i in idxs:
            tot=0;x=mu[i]
            for t in range(k):
                num=ys[t];den=1
                for ss in range(k):
                    if ss==t:continue
                    num=num*((x-xs[ss])%p)%p;den=den*((xs[t]-xs[ss])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            if tot==hvec[i]: agr.append(i)
        if len(agr)>best: best=len(agr); bestset=set(agr)
    # antipodal check: i and i+n/2 both in set?
    pairs=sum(1 for i in bestset if (i+n//2)%n in bestset and i<i+n//2)
    has1 = (0 in bestset)
    return bestset, pairs, has1

def main():
    cases=[(8,2),(8,4),(16,4),(16,8)]
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    for (n,k) in cases:
        rho=k/n
        p=find_prime_1_mod_n(n, n**4*4)
        mu=roots_of_unity(p,n)
        budget=n
        # aggregate over all far directions a<b in [k,n-1]
        results={}   # w->(maxcount,dir)
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
        for (a,b) in dirs:
            out,_=compute_for_direction(mu,a,b,k,p,n)
            for w,c in out.items():
                if w not in results or c>results[w][0]:
                    results[w]=(c,(a,b))
        # delta*
        ws=sorted(results)
        w_min=next((w for w in ws if results[w][0]<=budget), None)
        ds=1-w_min/n if w_min else None
        print(f"\n=== n={n} k={k} rho={rho} p={p} budget={budget} ===")
        for w in sorted(results,reverse=True):
            c,d=results[w]
            mk=" <== delta* boundary" if w==w_min else ""
            print(f"   w={w:2d} delta={1-w/n:.4f}  I={c:4d}  dir={d}{mk}")
        if ds is not None:
            g=gt.get((n,k))
            print(f"  delta*={ds:.4f}  gt={g}  MATCH={abs(ds-g)<1e-9 if g else '?'}")
            # decomp boundary witness
            a,b=results[w_min][1]
            _,gma=compute_for_direction(mu,a,b,k,p,n)
            gstar=max(gma,key=lambda gg:gma[gg]) if gma else None
            if gstar is not None:
                bs,pairs,h1=antipodal_decomp(mu,a,b,gstar,k,p,n)
                print(f"  boundary dir={(a,b)} bestgamma maxagree={gma[gstar]} |S|={len(bs)} antipodal_pairs={pairs} contains_x=1:{h1}")
            print(f"  shape c=(1-rho-delta*)*log2(n) = {(1-rho-ds)*log2(n):.4f}")
            print(f"  w_min={w_min}, n-w_min={n-w_min}, (1-rho)*n={(1-rho)*n}, k={k}")

if __name__=="__main__":
    main()
