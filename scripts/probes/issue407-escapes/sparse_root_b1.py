import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log

# ============================================================================
# SPARSE-ROOT THEORY attack on R-thin / B1, settling comment-142 vs 125 tension.
#
# The agreement polynomial P = X^a + gamma X^b - c(x), c of degree < k.
# Its roots inside mu_n are the agreement set S.
# Ragged (isolated) part = S minus all maximal mu_d-coset families.
#
# Sparse-root theory (Schlickewei-Evertse / Beukers-Smyth):
#   #isolated roots in mu_n of a t-term P depends only on t=#terms, not n.
#
# CRITICAL QUESTION (comment 125): is the binding direction the LOW-exponent
# x^k (far iff k <= (b mod n) < (1-delta)n), and does its ragged-count secretly
# = BGK ("combinatorial clothing")?  Or genuine off-BGK char-free?
#
# We compute the ACTUAL max ragged agreement size over ALL one-codeword agreement
# sets, for the binding LOW-exponent direction, char-0 (complex) AND char-p.
# ============================================================================

def primitive_root_mod_p(p):
    # find a generator of F_p^*
    if p == 2: return 1
    fac = []
    phi = p-1; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    return None

def find_prime_with_mu_n(n, lo, hi):
    # find prime p in [lo,hi] with n | p-1 (so mu_n exists in F_p)
    from sympy import isprime
    primes=[]
    # p = 1 + n*t
    t = (lo-1)//n
    while True:
        p = 1 + n*t
        if p>hi: break
        if p>=lo and isprime(p):
            primes.append(p)
        t+=1
    return primes

# --- char-p exact ragged-agreement computation over F_p ---
def mu_n_subgroup(p, n, g):
    # mu_n = { g^{(p-1)/n * j} } , j=0..n-1
    e = (p-1)//n
    base = pow(g, e, p)
    return [pow(base, j, p) for j in range(n)]

def max_ragged_for_low_direction(p, n, k, b, g, sample_cap=200000):
    """
    For monomial direction x^b (LOW exponent, b mod n in [k, n)), count the max
    agreement of x^b with a single degree-<k codeword over mu_n, and the ragged part.
    Agreement at point x in mu_n:  P(x) = x^b  where P deg < k.
    The agreement SET is { x in mu_n : there EXISTS deg-<k P matching }? No --
    we fix one codeword (one P) and count |{x: P(x)=x^b}|, maximize over P.
    Equivalent: maximize # of mu_n points where x^b - P(x) = 0, P deg < k.
    x^b - P has support {b mod n via reduction... } -- on mu_n, x^b = x^{b mod n}.
    So define Q(x) = x^{b mod n} - P(x), deg = max(b mod n, deg P) = b mod n (since b mod n >= k > deg P).
    #roots of Q in mu_n <= b mod n (degree bound). Max agreement = b mod n is achievable
    iff we can choose P so Q has b mod n roots all in mu_n -- i.e. Q = prod over a (b mod n)-subset
    of mu_n, but Q must be MONIC x^{bmodn} - (low deg). That's a CONSTRAINT: Q = x^m - P, deg P<k,
    means coeffs of x^{m-1},...,x^k of Q are ALL ZERO. So Q is x^m + (deg<k tail). 
    The agreement set S = roots of Q in mu_n is realized by ONE such Q.
    RAGGED = S not a union of mu_d cosets.
    """
    m = b % n
    if m < k:  # not eligible far / degree too low
        return None
    mu = mu_n_subgroup(p, n, g)
    muset = set(mu)
    # We want max over deg-<k P of |{x in mu_n : x^m = P(x) mod p}|, with raggedness.
    # The realizability constraint: S subset mu_n, |S|=s, is achievable as roots of
    # x^m - P (deg P<k) iff the monic poly prod_{x in S}(x - x_i) has its
    # coefficients of degrees k,...,m-1 all equal to ZERO (so that x^m - that = deg<k).
    # i.e. prod_{x in S}(X - x) = X^m - (deg < k poly). |S| must = m (degree m).
    # So S is a SIZE-m subset of mu_n whose elementary symmetric polys e_1..e_{m-k} vanish mod p.
    # That's m-k constraints. Generic solution count: search.
    # For tractability enumerate subsets only for small n.
    # We instead directly: any size-m subset S of mu_n with e_j(S)=0 for j=1..m-k gives a codeword.
    # Max agreement is then m IF such S exists. Ragged = is S a coset union?
    best = 0
    best_ragged = 0
    # Enumerate m-subsets is C(n,m); only feasible small n. We do it for n<=24.
    if comb(n, m) > sample_cap:
        return ('too_big', m, comb(n,m))
    # represent mu by exponents 0..n-1 (discrete log); x_i = base^{e_i}
    e_exp = (p-1)//n
    base = pow(g, e_exp, p)
    powers = [pow(base, j, p) for j in range(n)]  # mu_n indexed by exponent
    # elementary symmetric via Newton? Just compute coeffs of prod(X - powers[j]) mod p for subset
    found_ragged_sizes = []
    for sub in combinations(range(n), m):
        # poly coeffs (monic) prod (X - powers[j]) mod p
        coeffs = [1]
        for j in sub:
            xj = powers[j]
            new = [0]*(len(coeffs)+1)
            for i,c in enumerate(coeffs):
                new[i] = (new[i] + c) % p          # X * coeffs (shift)
            # actually do: coeffs * (X - xj)
            new = [0]*(len(coeffs)+1)
            for i,c in enumerate(coeffs):
                new[i+1] = (new[i+1] + c) % p       # *X
                new[i]   = (new[i]   - c*xj) % p     # *(-xj)
            coeffs = new
        # coeffs[i] = coeff of X^i, length m+1, coeffs[m]=1 (monic)
        # need coeffs[k..m-1] all zero (so prod = X^m + deg<k)
        if all(coeffs[i] % p == 0 for i in range(k, m)):
            # this subset is an agreement set; check raggedness (coset union?)
            ssub = set(sub)
            ragged = True
            for d in range(2, n+1):
                if n % d == 0:
                    # mu_d coset union? S closed under +n/d shift in exponent
                    shift = n//d
                    if all(((j+shift)%n) in ssub for j in ssub):
                        ragged = False
                        break
            sz = m
            if ragged:
                found_ragged_sizes.append(sz)
            best = max(best, sz)
    return (best, max(found_ragged_sizes) if found_ragged_sizes else 0, m, len(found_ragged_sizes))

# Run for small n at the binding LOW direction b = k (lowest far exponent), char-p
from sympy import isprime
print("=== char-p ragged agreement for LOW-exponent binding direction b=k ===")
print("n  k  m=bmodn  prime  maxAgree  maxRagged  #raggedSets  Johnson=sqrt(nk)")
for n in [8, 12, 16]:
    g = None
    # pick a thin prime p ~ large, n | p-1
    ps = find_prime_with_mu_n(n, 500, 5000)
    if not ps: continue
    p = ps[len(ps)//2]
    g = primitive_root_mod_p(p)
    for rho_den in [2,4]:
        k = max(1, n//rho_den)
        b = k  # binding low direction: lowest eligible far exponent
        m = b % n
        if m < k or m == 0: 
            continue
        res = max_ragged_for_low_direction(p, n, k, b, g)
        if res is None: continue
        if res[0]=='too_big':
            print(f"{n} {k} {m} {p}  (C(n,m)={res[2]} too big)")
            continue
        best, maxrag, mm, cnt = res
        print(f"{n:2d} {k:2d} {mm:2d}      {p:5d}  {best:3d}      {maxrag:3d}       {cnt:4d}        {sqrt(n*k):.2f}")
