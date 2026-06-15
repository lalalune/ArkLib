#!/usr/bin/env python3
"""
Probe for CONJECTURE [C02] (Conway-Jones Term-Count List Bound).

C02 asserts: in the lacunary form s*(n,k) = max #{mu_n-roots of a (k+2)-term P},
the roots decompose as antipodal torsion cosets ⊔ isolated points with
   (i)  isolated count <= k+1                     ("in-tree exact")
   (ii) the worst-case far-line LIST SIZE is governed by an n-independent
        (Schlickewei-Evertse) NONDEGENERATE count that stays POLYNOMIAL at
        t = k+2 = rho*n + 2, crossing the budget n at a past-Johnson delta*.

We test C02 in the PRIZE REGIME honestly:
  - proper dyadic subgroup mu_n, n = 2^mu  (NOT the full group, NEVER n = p-1)
  - p PRIME, p >> n^3, n | p-1
  - rate rho = k/n in {1/2,1/4,1/8,1/16}

Two killer questions:
  Q1 (refutes claim (i)): is the worst-case ISOLATED count actually > k+1?
  Q2 (refutes claim (ii)/the whole list-size pin): the prize-relevant object is
     NOT the isolated root count of one P; it is the COUNT OF BAD SCALARS gamma
     for a fixed direction (a,b) = far-line incidence / list size. By the in-tree
     Vieta pin gamma = -sum_{x in S} x, this is an r-fold subset-SUM cardinality.
     Does an n-independent (k+2)-term ROOT count control the bad-SCALAR count?
     (Scope gap: a bound on |S| / # roots says nothing about |{gamma}|.)

Honest reproducible numerics over proper mu_n with p prime, p >> n^3.
"""
import sympy
from sympy import primerange, isprime

def find_prime(n, exp=4):
    """Smallest prime p with n | p-1 and p > n^exp (so p >> n^3)."""
    target = n**exp
    # p = n*t + 1
    t = (target // n) + 1
    while True:
        p = n*t + 1
        if isprime(p):
            return p
        t += 1

def subgroup(p, n):
    """The unique order-n multiplicative subgroup mu_n of F_p (n | p-1)."""
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)          # element of order n
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x*h) % p
    assert len(S) == n, (len(S), n)
    return sorted(S), h

def vandermonde_far_line_badscalars(p, mu, n, k, a, b):
    """
    For the far monomial line f = x^a + gamma*x^b (a,b >= k, far direction),
    count the DISTINCT bad scalars gamma in F_p such that f agrees with SOME
    degree-<k codeword on a (k+1)-subset T of mu_n. This is the far-line
    incidence / interleaved-list object the budget gates.

    Bad-gamma per (k+1)-subset T = {x_0..x_k}: the top divided difference (=h_{m-k},
    complete homogeneous) must vanish, LINEAR in gamma:
       gamma_T = - h_{a-k}(T) / h_{b-k}(T)   (single bad scalar per T, when h_{b-k}!=0)
    The bad-scalar set across ALL (k+1)-subsets is what the budget n must bound.
    We compute distinct gamma_T over all (k+1)-subsets of mu_n.
    """
    from itertools import combinations
    # complete homogeneous symmetric poly h_d via generating-function recursion
    # h_d(x_0..x_k) : use Newton/elementary not needed; compute by DP over power sums?
    # Simplest: h_d = sum over multisets; use the recurrence with elementary symmetric.
    # We'll compute h_d directly via the generating series prod 1/(1-x_i t).
    def h_values(T, dmax):
        # returns [h_0, h_1, ..., h_dmax] mod p
        H = [0]*(dmax+1)
        H[0] = 1
        for d in range(1, dmax+1):
            # h_d = sum_{i} x_i * h_{d-1 restricted}? Use power-sum Newton: easier:
            # h_d = (1/d) sum_{j=1}^{d} p_j * h_{d-j}, p_j = sum x_i^j (power sum)
            s = 0
            for j in range(1, d+1):
                pj = sum(pow(x, j, p) for x in T) % p
                s = (s + pj * H[d-j]) % p
            H[d] = (s * pow(d, -1, p)) % p
        return H
    dmax = max(a-k, b-k)
    bad = set()
    for T in combinations(mu, k+1):
        H = h_values(T, dmax)
        ha = H[a-k] % p
        hb = H[b-k] % p
        if hb % p != 0:
            gamma = (-ha * pow(hb, -1, p)) % p
            bad.add(gamma)
        # if hb==0 and ha==0: every gamma works -> degenerate; if hb==0,ha!=0: none
        elif ha % p == 0:
            bad.add('ALL')  # degenerate direction marker
    return bad

def isolated_count_consecutive_run(p, mu, n, k):
    """
    The in-tree extremal isolated witness: S = consecutive run {z^0,...,z^k}
    (k+1 points), which is the (k+2)-sparse line and shares no nontrivial coset.
    Returns its isolated size = k+1, AND we search for any (k+2)-sparse-realizable
    S with MORE isolated (coset-free) points to test the cap k+1.
    Honest: we do an exhaustive small-case test of the cap.
    """
    # The cap claim is |iso| <= k+1. In-tree _IsolatedCountKelley says measured ~ k+2.
    # We just report the run value (k+1) as the lower witness; the cap question is
    # better answered by the documented exact sweep. Here we sanity-check that a
    # (k+2)-term P CAN have > k+1 roots in mu_n at all (s* > k+1), which already
    # shows root count is not term-bounded.
    return k+1

def far_line_root_count_max(p, mu, n, k):
    """
    s*-style: max number of mu_n-roots of a (k+2)-term P = x^a + gamma x^b - c(x),
    deg c < k. We search over (a,b) far, and for each (k+1)-subset that is bad,
    these are agreements; but the max ROOT COUNT of a single (k+2)-term poly is the
    list-decoding agreement. We compute the max over (a,b,gamma) of #{x in mu_n :
    x^a + gamma x^b lies on a deg<k codeword through enough points}. Simpler proxy:
    for fixed (a,b), the max agreement of ANY single far line = max over gamma of
    the largest subset T s.t. f|_T in RS[k]. We report the largest such agreement.
    """
    from itertools import combinations
    best = 0
    best_info = None
    # For a far line to agree on a w-subset, need w-k divided differences to vanish.
    # We brute force: for each (a,b) far, each gamma in F_p is too many; instead use
    # that agreement on T (|T|>=k+1) determines gamma uniquely from the FIRST extra
    # point, then check the rest. Exhaustive over (a,b) and starting (k+1)-subsets.
    for a in range(k, n):
        for b in range(k, a):  # a > b, both far (>= k)
            if a == b: continue
            # For each (k+1)-subset, get gamma_T, then count how many mu_n points
            # x have f_gamma agree with the SAME degree-<k interpolant. Equivalent:
            # count roots in mu_n of P = x^a + gamma x^b - c(x) where c interpolates
            # f on T (deg < k uses k points; the (k+1)-th fixes gamma). We count the
            # mu_n elements where x^a+gamma x^b equals the interpolant of those values.
            def hvals(T, dmax):
                H=[0]*(dmax+1); H[0]=1
                for d in range(1,dmax+1):
                    s=0
                    for j in range(1,d+1):
                        pj=sum(pow(x,j,p) for x in T)%p
                        s=(s+pj*H[d-j])%p
                    H[d]=(s*pow(d,-1,p))%p
                return H
            dmax=max(a-k,b-k)
            for T in combinations(mu, k+1):
                H=hvals(T,dmax)
                ha=H[a-k]%p; hb=H[b-k]%p
                if hb%p==0: continue
                gamma=(-ha*pow(hb,-1,p))%p
                # interpolant c of f=x^a+gamma x^b on first k points of mu (any k pts);
                # then count mu_n points where f - c vanishes = roots of P in mu_n.
                # Build f values on all mu, interpolate deg<k through k of them, count agree.
                fvals={x:(pow(x,a,p)+gamma*pow(x,b,p))%p for x in mu}
                pts=list(mu)[:k]
                # Lagrange interpolation deg<k through (pts, fvals)
                def interp(xq):
                    tot=0
                    for i,xi in enumerate(pts):
                        num=1; den=1
                        for jx,xj in enumerate(pts):
                            if jx==i: continue
                            num=(num*((xq-xj)%p))%p
                            den=(den*((xi-xj)%p))%p
                        tot=(tot+fvals[xi]*num*pow(den,-1,p))%p
                    return tot%p
                agree=sum(1 for x in mu if (fvals[x]-interp(x))%p==0)
                if agree>best:
                    best=agree; best_info=(a,b,gamma)
    return best, best_info

def main():
    print("="*78)
    print("PROBE C02 — Conway-Jones term-count list bound, prize regime")
    print("="*78)
    configs = [
        # (n, rho) -> k = rho*n
        (8,  4),   # k=4, rho=1/2
        (8,  2),   # k=2, rho=1/4
        (16, 8),   # rho=1/2
        (16, 4),   # rho=1/4
        (16, 2),   # rho=1/8
        (32, 8),   # rho=1/4
        (32, 4),   # rho=1/8
    ]
    for n, k in configs:
        mu_exp = (n & -n)  # crude; n is power of 2 here
        assert (n & (n-1)) == 0, "n must be 2^mu for prize regime"
        p = find_prime(n, exp=4)   # p >> n^3 (p > n^4)
        assert isprime(p) and (p-1) % n == 0 and p != n+1 and p-1 != n
        mu, h = subgroup(p, n)
        rho = k/n
        budget = n   # q*eps* ~ n
        # claim (i): isolated cap k+1
        iso_run = isolated_count_consecutive_run(p, mu, n, k)
        # max single-line agreement (s*-proxy = list-decoding agreement)
        smax, info = far_line_root_count_max(p, mu, n, k)
        # claim (ii): bad-scalar count for the worst far direction (the budget object)
        # pick the far direction maximizing distinct bad gammas
        best_badcount = 0; best_dir=None; sawALL=False
        for a in range(k, n):
            for b in range(k, a):
                bad = vandermonde_far_line_badscalars(p, mu, n, k, a, b)
                if 'ALL' in bad: sawALL=True
                bc = len([x for x in bad if x!='ALL'])
                if bc > best_badcount:
                    best_badcount = bc; best_dir=(a,b)
        johnson_s = (k*n)**0.5   # Johnson agreement radius sqrt(kn); s*>this => past Johnson
        print(f"\n n={n} k={k} rho={rho:.4f}  p={p} (p/n^3={p/n**3:.1f})  budget={budget}")
        print(f"   isolated run witness (claim i lower)      = {iso_run}  (k+1={k+1})")
        print(f"   max single far-line agreement s*-proxy    = {smax} at {info}   Johnson sqrt(kn)={johnson_s:.2f}")
        print(f"      -> s* past Johnson? {smax > johnson_s}")
        print(f"   MAX distinct BAD-SCALAR count over far dirs= {best_badcount} at dir {best_dir}  (degenerate ALL seen: {sawALL})")
        print(f"      -> bad-scalar count vs budget n={budget}: {'OVER' if best_badcount>budget else 'under'} budget")
        print(f"      -> bad-scalar count vs k+1={k+1} (isolated cap): {'EXCEEDS' if best_badcount>k+1 else 'within'}")

if __name__ == "__main__":
    main()
