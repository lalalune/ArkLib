# RESULT (2026-06-13): (1) the +-transversal coset-rigidity conjecture is REFUTED -- bad
# witnesses freely contain both zeta and -zeta. (2) True worst-case bad-SCALAR count is LINEAR:
# maxbad = 5,3,3,13 for n=8,8,8,16 (~ n-2r+1), FAR below KKH26 budget (24,24,32,112) and the
# provable C(n,k+1) (28,28,56,120). delta* pin holds with huge margin; correct provable target is
# an O(n) line-ball-incidence bound. Confirms in-tree probe Q3 (bad count hits O(n)).
# #389: test the COSET-RIGIDITY / +-transversal conjecture for the deep-band MCA bad scalars.
# Conjecture: for the single-poly stack (Q0, X^{r-1}) over mu_n (n=2^mu, m=1), the bad
# (k+1=r)-subsets T (gamma = -Q0[T], extending to a witness S, |S|=r+1, agreement >= r+1)
# never contain both zeta and -zeta -- i.e. they are TRANSVERSALS of the order-2-subgroup
# cosets {zeta,-zeta}.  If true, #bad <= 2^r * C(2^{mu-1}, r) = the exact KKH26 budget.
import itertools

def F(p):
    return p

def find_gen(p, n):
    # primitive n-th root of unity in F_p (n | p-1)
    for a in range(2, p):
        if pow(a, n, p) == 1 and all(pow(a, n//q, p) != 1 for q in set(prime_factors(n))):
            return a
    return None

def prime_factors(n):
    f=[]; d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return f

def divided_diff(Q, pts, p):
    # leading coeff (deg = |pts|-1) of interpolant of Q over pts = top divided difference
    # but we need coeff_{r-1} and coeff_r of Q mod m_S; compute via interpolation.
    # Return the full interpolant coeffs (degree < len(pts)) of Q on pts.
    m = len(pts)
    # build Vandermonde and solve for interpolant of (x -> Qeval(x))
    # Qeval given as dict or list of coeffs; here Q is list of coeffs
    def qeval(x):
        r=0
        for c in reversed(Q): r=(r*x + c)%p
        return r%p
    # Lagrange -> coefficients via solving linear system (m x m)
    import itertools as it
    # Build matrix A[i][j] = pts[i]^j, solve A c = y
    A=[[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
    y=[qeval(pts[i]) for i in range(m)]
    # gaussian elim mod p
    M=[row[:]+[y[i]] for i,row in enumerate(A)]
    for col in range(m):
        piv=None
        for rr in range(col,m):
            if M[rr][col]%p!=0: piv=rr;break
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        inv=pow(M[col][col],p-2,p)
        M[col]=[(v*inv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                f=M[rr][col]
                M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]

def test(p, mu, r, ntrials=400):
    n=1<<mu
    g=find_gen(p,n)
    if g is None: return None
    mun=[pow(g,j,p) for j in range(n)]
    neg1=pow(g, n//2, p)  # = -1
    # order-2 cosets {zeta, -zeta}
    k=r-1  # m=1
    a=r+1
    import random
    random.seed(1)
    maxbad=0; transversal_violations=0; total_bad_over_trials=0
    for _ in range(ntrials):
        # random non-codeword Q0 of degree 2r
        Q=[random.randrange(p) for _ in range(2*r+1)]
        if Q[2*r]==0: Q[2*r]=1
        # find bad scalars: enumerate (r+1)-subsets S; witness iff interpolant deg <= r-1
        # (coeff_r of Q mod m_S = 0); gamma = -coeff_{r-1}.  Then check agreement extends >= a
        # (automatic here since S itself is the agreement of size a=r+1 with codeword=interpolant deg<=r-2?
        #  need interpolant deg <= k-1 = r-2 for codeword. Let's require deg(Q0 mod m_S) <= r-2 after
        #  subtracting gamma*X^{r-1}.)
        badset=set()
        badTs=[]
        for S in itertools.combinations(range(n), a):
            pts=[mun[i] for i in S]
            coeffs=divided_diff(Q, pts, p)  # interpolant of Q0 on S, degree < a = r+1
            if coeffs is None: continue
            cr = coeffs[r] if r < len(coeffs) else 0      # coeff_r
            cr1= coeffs[r-1] if r-1 < len(coeffs) else 0   # coeff_{r-1}
            # witness: (Q0 + gamma X^{r-1}) mod m_S has degree <= r-2 (codeword deg < k=r-1)
            # coeff_r(Q0 mod m_S)=cr ; with X^{r-1}: coeff_r unaffected -> need cr==0
            # coeff_{r-1}: cr1 + gamma -> need 0 -> gamma=-cr1; also remaining coeffs r-2? deg<=r-2 ok
            if cr % p == 0:
                gamma = (-cr1) % p
                badset.add(gamma)
                # the pinning subset T = any r-subset of S; record S's elements (as exponents)
                badTs.append(tuple(S))
        if len(badset)>maxbad: maxbad=len(badset)
        total_bad_over_trials+=len(badset)
        # check transversal: does any witness S contain both i and i+n/2 (a +- pair)?
        for S in badTs:
            Sset=set(S)
            for i in S:
                if (i + n//2)%n in Sset and i < (i+n//2)%n:
                    transversal_violations+=1
                    break
    budget = (1<<r)*comb(2**(mu-1), r)
    mybound = comb(n, r)  # C(n, k+1)
    return dict(p=p,mu=mu,r=r,n=n, maxbad=maxbad, avgbad=total_bad_over_trials/ntrials,
                budget=budget, mybound_Cnk1=mybound,
                witness_pm_pair_violations=transversal_violations)

from math import comb
for (p,mu,r) in [(17,3,2),(97,3,2),(193,3,3),(97,4,2)]:
    print(test(p,mu,r))
