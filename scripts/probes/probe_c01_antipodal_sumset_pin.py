#!/usr/bin/env python3
"""
probe_c01_antipodal_sumset_pin.py  (#444 / issue C01)

ATTACK on CONJECTURE C01: "Antipodal Sumset Saturation Pin".

C01 claims:
  - the worst-case far-line list-size crossing happens at
        w <= k + log2( n / gcd(b-a, n) )                                (C01-A)
  - maximizing over gcd(b-a,n)=1 (so d = n/gcd = n) pins
        delta* = (1 - rho) - log2(n)/n                                  (C01-B)
    which (C01 asserts) exceeds Johnson 1-sqrt(rho).

The campaign already refuted delta*=(1-rho)-log2(n)/n at n=64 (commit ce8cb602e,
true law s*-k = n/4 => delta* = 3/4 - rho).  This probe independently RE-DERIVES
the worst-case char-0 far-line incidence and tests C01's TWO specific structural
predictions head-on:

  (P1) Is the worst (incidence-maximizing) direction gcd(b-a,n)=1, as C01 needs?
  (P2) Does the crossing offset s*-k = log2(n/gcd) (C01) or = n/4 (campaign)?

METHOD (char-0 faithful, p-independent; PROPER subgroup mu_n < F_p*, p prime,
p >> n^3, NEVER n=p-1).  A far line is the pencil  x^a + gamma x^b  restricted to
mu_n.  A scalar gamma is "bad at threshold t" iff that pencil agrees with some
codeword of RS[mu_n, k] on >= t points.  Agreement on a t-subset S forces the
order-k divided differences over S to vanish; each is AFFINE in gamma, so per
(k+1)-subset there is <= 1 candidate gamma.  We count, per pencil, the max number
of gamma achieving agreement t = exact bad-scalar list size at radius delta=1-t/n.
We sweep t down from n and record the FIRST t where some far pencil's list size
exceeds the budget (~ n); s* = that t; delta* = 1 - s*/n; offset = s* - k.

We verify p-independence with two primes per (n,k) to certify char-0 faithfulness.
"""
import sys, itertools, math
from sympy import isprime, primitive_root

def find_prime_with_subgroup(n, beta_min=3.0, beta_max=6.0):
    """Find prime p, p>>n^3, n | p-1, p prime, NOT n=p-1 (proper subgroup)."""
    lo = max(int(n**beta_min), n*n*n*8)
    p = lo
    while True:
        p += 1
        if (p - 1) % n != 0:
            continue
        if not isprime(p):
            continue
        if p - 1 == n:          # forbid full group
            continue
        # ensure proper subgroup, p>>n^3
        if p > n**beta_max:
            raise RuntimeError("no prime in band")
        return p

def subgroup(n, p):
    """Return the n-element multiplicative subgroup mu_n of F_p* as a list (ints)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)        # generator of mu_n
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x * h) % p
    assert len(set(elts)) == n, "mu_n not size n"
    return elts, p

def far_line_badcount(a, b, gammas_universe, mu, k, t, p):
    """
    EXACT bad-scalar count at agreement threshold t for pencil x^a + gamma x^b on mu.
    A gamma is bad iff exists codeword c in RS[mu,k] with #{x in mu : c(x) = x^a+gamma x^b} >= t.
    We use the (k+1)-subset divided-difference engine: pick t-subset S; the values
    v_i = x_i^a + gamma x_i^b on S must be interpolated by a deg<k poly => all order-k
    divided differences vanish.  Each DD is affine in gamma: A + gamma B = 0.  Over the
    (t-k) independent DD windows we get a consistent linear system => at most one gamma.
    We iterate over t-subsets, solve for gamma, collect feasible gammas (in F_p).
    Returns set of bad gammas (excluding gamma=0 trivial via membership note).
    """
    n = len(mu)
    bad = set()
    idx = list(range(n))
    # Precompute powers
    xa = [pow(x, a, p) for x in mu]
    xb = [pow(x, b, p) for x in mu]
    inv = [pow(x % p, p-2, p) for x in mu]
    for S in itertools.combinations(idx, t):
        xs = [mu[i] for i in S]
        Va = [xa[i] for i in S]   # constant part of value
        Vb = [xb[i] for i in S]   # coefficient of gamma
        # order-k divided differences of the value-vector (affine in gamma) must vanish.
        # Build DD table symbolically as (const, gammacoef) pairs.
        m = len(S)
        # f[i] = (Va[i], Vb[i])  representing value = const + gamma*coef
        f = [(Va[j] % p, Vb[j] % p) for j in range(m)]
        cols = [f]
        ok = True
        for order in range(1, k+1):
            prev = cols[-1]
            newcol = []
            for j in range(m - order):
                xj = xs[j]; xjo = xs[j+order]
                denom = (xjo - xj) % p
                if denom == 0:
                    ok = False; break
                dinv = pow(denom, p-2, p)
                c = ((prev[j+1][0] - prev[j][0]) * dinv) % p
                d = ((prev[j+1][1] - prev[j][1]) * dinv) % p
                newcol.append((c, d))
            if not ok: break
            cols.append(newcol)
        if not ok:
            continue
        # The order-k DD column (cols[k]) must all be zero: const + gamma*coef == 0
        ddk = cols[k]
        gamma_sol = None
        consistent = True
        for (c, d) in ddk:
            if d % p == 0:
                if c % p != 0:
                    consistent = False; break
                # 0==0 : no constraint
            else:
                g = (-c * pow(d, p-2, p)) % p
                if gamma_sol is None:
                    gamma_sol = g
                elif gamma_sol != g:
                    consistent = False; break
        if not consistent:
            continue
        if gamma_sol is None:
            # all DDs vacuous: pencil itself low-degree on S for every gamma -> degenerate
            continue
        bad.add(gamma_sol)
    return bad

def worst_far_incidence(n, k, p, mu, budget):
    """
    Sweep threshold t from n down; for each t find max-over-far-pencils bad-count.
    Far pencil: a != b, both can range; 'far' direction = the pencil isn't a codeword
    direction (a >= k or b >= k).  Returns dict t -> (maxcount, best_pencil, gcd_of_diff).
    """
    results = {}
    # restrict pencils: WLOG a in [0..n-1], b in [0..n-1], a<b, far means max(a,b)>=k
    pencils = [(a, b) for a in range(n) for b in range(a+1, n) if max(a, b) >= k]
    for t in range(n, k, -1):
        best = -1; bestpen = None; bestgcd = None
        for (a, b) in pencils:
            bad = far_line_badcount(a, b, None, mu, k, t, p)
            cnt = len(bad)
            if cnt > best:
                best = cnt; bestpen = (a, b); bestgcd = math.gcd((b-a) % n, n)
        results[t] = (best, bestpen, bestgcd)
        # stop once we've gone well past the crossing
    return results

def analyze(n, k, betas=(3.2, 4.0)):
    print(f"\n===== n={n}, k={k}, rho={k}/{n}={k/n:.4f} =====")
    primes = []
    p = max(int(n**betas[0]), 8*n*n*n)
    # collect two distinct primes p>>n^3, proper subgroup
    found = []
    cand = p
    while len(found) < 2 and cand < n**6:
        cand += 1
        if (cand-1) % n == 0 and isprime(cand) and (cand-1) != n:
            found.append(cand)
    budget = n
    all_res = {}
    for pp in found:
        mu, _ = subgroup(n, pp)
        beta = math.log(pp)/math.log(n)
        res = worst_far_incidence(n, k, pp, mu, budget)
        all_res[pp] = res
        print(f"  p={pp} (beta={beta:.2f}, proper mu_{n}):")
        # find crossing: largest t with maxcount > budget
        sstar = None
        for t in range(k+1, n+1):
            if res[t][0] > budget:
                sstar = t
        # report a window around crossing
        for t in sorted(res.keys(), reverse=True):
            mc, pen, g = res[t]
            mark = " <== first BAD (>budget)" if (mc > budget and (t == sstar)) else ""
            if mc > 0:
                print(f"    t={t:2d} (delta={1-t/n:.4f}): maxcount={mc:4d} pencil={pen} gcd(b-a,n)={g}{mark}")
        if sstar is not None:
            offset = sstar - k
            log2d_at_worst = None
            _, pen, g = res[sstar]
            d = n // g
            print(f"    => s*={sstar}, offset s*-k={offset}, worst gcd(b-a,n)={g}, d=n/gcd={d}, log2(d)={math.log2(d):.2f}, n/4={n/4}")
            print(f"       C01 predicts offset = log2(d) = {math.log2(d):.2f}; campaign predicts offset = n/4 = {n/4}")
    # p-independence check
    if len(found) == 2:
        r0 = all_res[found[0]]; r1 = all_res[found[1]]
        agree = all(r0[t][0] == r1[t][0] for t in r0)
        print(f"  p-INDEPENDENCE (char-0 faithful): {'YES' if agree else 'NO'} across p={found}")

if __name__ == "__main__":
    # rho=1/8 row (the row C01's log2(n) was fit to), at the two computable sizes
    analyze(16, 2)   # rho=1/8
    analyze(32, 2)   # rho=1/8 ; campaign showed offset 5=log2(32) here (coincidence)
    # rho=1/4 control: C01 must hold rate-uniformly
    analyze(16, 4)   # rho=1/4
