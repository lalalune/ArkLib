#!/usr/bin/env python3
"""
A8 LOWER BOUND on delta*(n,rho): incidence I(delta) <= budget=n below a candidate edge.

STRATEGY. delta* = sup{ delta : max_dir I(delta) <= n }.  delta = 1 - w/n, w = agreement size.
As w grows (delta shrinks toward 0) I shrinks; the LOWER bound on delta* is the (1 - w_cross/n)
where w_cross is the SMALLEST w with max_dir I(w) <= n.  A8 wants: prove I(w) <= n for all
w >= w_edge(n,rho), i.e. delta <= 1 - w_edge/n, by bounding the number of consistent dilation
orbits.

KEY STRUCTURAL FACT (established by a6 probe, reused here):
  Fix far direction (a,b), step=t=b-a, d=gcd(t,n), m=n/d (= dilation-orbit size on gamma).
  A w-subset S of mu_n is "consistent" for (a,b) iff x^a + gamma x^b in RS[k] on S for some gamma,
  i.e. the (k+2)-col generalized Vandermonde M=[x^0..x^{k-1},x^a,x^b] restricted to S is
  rank <= k+1 (rank-deficient).  The distinct bad gamma = distinct value of a rational symmetric
  invariant; bad set is a union of <zeta^t>-orbits (gamma -> zeta^t gamma), orbit size m.
  So  I(w) = (#dilation-orbits of bad gamma) * m  but counted as DISTINCT gamma it is
  #distinct invariant values.  This probe computes I(w) EXACTLY in char 0 (over Z[zeta_n]
  via exact-arithmetic rank test) for w from n down, finds the crossing, and tests upper-bound
  closed forms for I(w) to certify a LOWER bound delta* >= f.

We do the EXACT rank test over the cyclotomic field by using a big prime q == 1 mod n,
q >> n^4, low 2-adic valuation (faithful, p-independent over-det band). Verified vs second prime.

Honesty: PROPER subgroup (n | q-1, n < q-1).  Tag everything.
"""
import sys, itertools
from math import gcd, comb

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo, skip=0):
    q = ((lo // n) + 1) * n + 1
    found = 0
    an=n; v2n=0
    while an%2==0: an//=2; v2n+=1
    while True:
        if isprime(q):
            t = q-1; v2 = 0
            while t % 2 == 0: t//=2; v2+=1
            if v2 <= v2n + 2:
                if found == skip: return q
                found += 1
        q += n

def mu_table(n, q):
    e=(q-1)//n
    w=None
    for base in range(2,q):
        cand=pow(base,e,q)
        if cand==1: continue
        if pow(cand, n//2, q)==1: continue
        w=cand; break
    return [pow(w,i,q) for i in range(n)]

def rank_mod(rows, q):
    """rank over F_q of a list of row-vectors (mod q). Gaussian elimination."""
    rows=[r[:] for r in rows]
    R=len(rows);
    if R==0: return 0
    C=len(rows[0])
    rank=0; pr=0
    for c in range(C):
        piv=None
        for r in range(pr,R):
            if rows[r][c]%q!=0: piv=r; break
        if piv is None: continue
        rows[pr],rows[piv]=rows[piv],rows[pr]
        inv=pow(rows[pr][c],q-2,q)
        rows[pr]=[(x*inv)%q for x in rows[pr]]
        for r in range(R):
            if r!=pr and rows[r][c]%q!=0:
                f=rows[r][c]
                rows[r]=[(rows[r][i]-f*rows[pr][i])%q for i in range(C)]
        pr+=1; rank+=1
        if pr==R: break
    return rank

def bad_gamma(n,k,a,b,S,mu,q):
    """Return the (set of) bad gamma for subset S in F_q, or None if not consistent.
    Consistent iff M=[1,x,..,x^{k-1}, x^a, x^b] on S has rank <= k+1.
    If rank == k+1 generically there is a UNIQUE gamma (col x^a+gamma x^b in span of first k+? )
    We solve: does there exist gamma with [V | (x^a + gamma x^b)] rank <= k for the x^a col?
    Actually: f=x^a+gamma x^b agrees with deg<k poly on S iff (x^a+gamma x^b) in span{1..x^{k-1}} on S.
    => exists gamma s.t. col_a + gamma col_b in colspace(V_k).  Solve least structure:
       residual r_a = proj of col_a off V_k ; r_b similarly; need r_a + gamma r_b = 0 => gamma=-r_a/r_b
       and consistent iff r_a, r_b are parallel (r_a in span(r_b)).
    Over F_q we do it by rank tests:
       rank[V|col_a|col_b] and rank[V|col_b].
       consistent (exists gamma incl gamma=0 if col_a in V) iff
          rank[V|col_a|col_b] - rank[V|col_b] == 0  (col_a in span(V,col_b))  -- but need the
          combination to kill the x^b too with a SCALAR. Use the residual approach via solving.
    """
    xs=[mu[s%n] for s in S]
    Vk=[[pow(x,c,q) for c in range(k)] for x in xs]
    ca=[pow(x,a,q) for x in xs]
    cb=[pow(x,b,q) for x in xs]
    rVb=rank_mod([row+[cb[i]] for i,row in enumerate(Vk)],q)
    rVa=rank_mod([row+[ca[i]] for i,row in enumerate(Vk)],q)
    rVab=rank_mod([row+[ca[i],cb[i]] for i,row in enumerate(Vk)],q)
    rV=rank_mod([row[:] for row in Vk],q)
    # need: exists scalar gamma with ca + gamma cb in colspace(Vk).
    # set W = colspace(Vk). ca,cb mod W are two vectors in quotient. need ca = -gamma cb mod W.
    # i.e. images of ca, cb in quotient are linearly dependent (parallel).
    # dim span(images of ca,cb) = rVab - rV.  parallel/zero  <=> rVab - rV <= 1.
    if rVab - rV <= 1:
        # solve gamma. residual approach via solving linear system for gamma:
        # find gamma s.t. ca+gamma cb in span(Vk). Build augmented: solve for coeffs.
        # Use: pick gamma by elimination. We solve over F_q the system V*y = ca + gamma cb has soln.
        # Equivalent: (ca+gamma cb) reduced against Vk basis is zero. Do symbolic in gamma:
        # reduce ca and cb against Vk simultaneously, track residuals; gamma = -resid_a/resid_b coord.
        ra,rb=reduce_pair(Vk,ca,cb,q)
        # ra + gamma rb == 0 in all coords. find gamma from a nonzero coord of rb.
        if all(v%q==0 for v in rb):
            if all(v%q==0 for v in ra): return 0  # col_a already in V (gamma arbitrary->treat gamma=0 family)
            return None
        gamma=None
        for i in range(len(rb)):
            if rb[i]%q!=0:
                gamma=(-ra[i]*pow(rb[i],q-2,q))%q
                break
        # verify all coords
        if all((ra[i]+gamma*rb[i])%q==0 for i in range(len(rb))):
            return gamma
        return None
    return None

def reduce_pair(Vk,ca,cb,q):
    """Row-reduce Vk and apply same ops to ca,cb (as extra columns); return residual cols
    (the parts of ca,cb not in colspace(Vk))."""
    R=len(Vk);
    if R==0: return [],[]
    C=len(Vk[0])
    M=[Vk[i][:]+[ca[i],cb[i]] for i in range(R)]
    pr=0; pivcols=[]
    for c in range(C):
        piv=None
        for r in range(pr,R):
            if M[r][c]%q!=0: piv=r;break
        if piv is None: continue
        M[pr],M[piv]=M[piv],M[pr]
        inv=pow(M[pr][c],q-2,q)
        M[pr]=[(x*inv)%q for x in M[pr]]
        for r in range(R):
            if r!=pr and M[r][c]%q!=0:
                f=M[r][c]; M[r]=[(M[r][i]-f*M[pr][i])%q for i in range(C+2)]
        pivcols.append(c); pr+=1
        if pr==R: break
    # residual of ca,cb = entries in rows below the pivot rows (rows pr..R-1), columns C,C+1
    ra=[M[r][C]%q for r in range(pr,R)]
    rb=[M[r][C+1]%q for r in range(pr,R)]
    return ra,rb

def I_of_w(n,k,a,b,w,mu,q):
    bad=set()
    for S in itertools.combinations(range(n),w):
        g=bad_gamma(n,k,a,b,S,mu,q)
        if g is not None and g!=0:   # gamma=0 excluded (direction must use x^b nontrivially)
            bad.add(g)
    return len(bad)

def worst_I_of_w(n,k,w,mu,q):
    best=0; bestdir=None
    for a in range(k,n):
        for b in range(a+1,n):
            I=I_of_w(n,k,a,b,w,mu,q)
            if I>best: best=I; bestdir=(a,b)
    return best,bestdir

def main():
    print("=== A8 LOWER BOUND: I(w) crossing of budget=n, worst direction ===")
    for (n,rho) in [(8,0.25),(8,0.5),(16,0.25),(16,0.5)]:
        k=int(round(rho*n))
        q=find_prime(n, n**4*4)
        q2=find_prime(n, n**4*4, skip=1)
        mu=mu_table(n,q); mu2=mu_table(n,q2)
        print(f"\n--- n={n} rho={rho} k={k} budget={n}  q={q} (check q2={q2}) ---")
        cross=None
        for w in range(n-1, k, -1):
            I,dir_=worst_I_of_w(n,k,w,mu,q)
            # p-independence check on the crossing region
            I2,_=worst_I_of_w(n,k,w,mu2,q2)
            tag = "OK" if I==I2 else f"!!P-DEP I2={I2}"
            le = I<=n
            print(f"  w={w:2d} delta={1-w/n:.4f}  worstI={I:4d} dir={dir_}  I<=n:{le}  [{tag}]")
            if le and cross is None:
                cross=w
            if not le and cross is not None:
                # found a smaller w that violates -> crossing not monotone; reset note
                print(f"     (non-monotone: I exceeds n at smaller w={w})")
        if cross is not None:
            print(f"  >> smallest w with worstI<=n down-scan first-hit gives delta* >= {1-cross/n:.4f} (w_edge={cross})")
    print("\nDONE")

if __name__=="__main__":
    main()
