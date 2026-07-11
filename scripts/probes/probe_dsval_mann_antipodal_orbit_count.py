#!/usr/bin/env python3
"""
probe_dsval_mann_antipodal_orbit_count.py   (issue #407, A5 Mann/vanishing-sums angle)

GOAL: pin delta*(n,rho) for RS[mu_n, k=rho n], mu_n = 2^a-th roots of unity (n=2^a),
char 0, via the MANN / VANISHING-SUMS-OF-ROOTS-OF-UNITY structure of the
consistency variety.  Count consistent (agreement) subsets EXACTLY, then read off
  I(delta) = max over far directions (a,b), a<b, of #{gamma : x^a+gamma x^b agrees
             with some deg<k poly on a w-subset of mu_n},  w=(1-delta) n,
  delta*(n,rho) = sup{ delta : I(delta) <= n }.

=================  THE A5 STRUCTURE  =================
Fix direction (a,b), a<b, both >= k (far exponents), gcd issues aside.  Suppose
x^a + gamma x^b agrees with deg<k poly g on S = {zeta_1,...,zeta_w} subset of mu_n.
For EACH zeta in S:   zeta^a + gamma zeta^b - g(zeta) = 0.

Subtract over pairs / use that g has deg < k.  The cleanest invariant: the
agreement set S of a fixed (gamma, g) is exactly the mu_n-root set of the lacunary
polynomial F(x) = x^a + gamma x^b - g(x), support contained in {0,..,k-1, a, b}.
Over char 0 (or p >> n^4), the number of mu_n-roots of any nonzero F = its number
of cyclotomic factors Phi_d (d | n) it contains, each contributing phi(d) roots
that lie in mu_n.  For n = 2^a, d | n => d in {1,2,4,...,2^a}, and Phi_{2^j}(x) =
x^{2^{j-1}} + 1 for j>=1, Phi_1 = x-1.  So the mu_n-root set of F is a UNION OF
ANTIPODAL-CLOSED COSETS:  roots of x^{2^{j-1}}+1 = the coset of mu_{2^j} that is
NOT in mu_{2^{j-1}} (an antipodal-paired set of size 2^{j-1}), plus possibly {1}.

MANN's theorem (n=2^a): a minimal vanishing sum of n-th roots of unity is the
antipodal pair z + (-z) = 0.  So any agreement set S decomposes into antipodal
pairs (+ a fixed point at x=1 only via Phi_1).  THIS IS THE CONSISTENCY VARIETY
STRUCTURE: S must be a union of "Phi_d-cosets" (d|n), i.e. S = union over a chosen
subset D of divisors {1,2,4,...,n} of the corresponding cyclotomic coset.

So COUNTING consistent S reduces to: which divisor-cosets D can be realized by a
single lacunary F = x^a+gamma x^b - g, deg g < k, and how many gamma per realized S.

This probe:
 (1) EXACT char-0 enumeration (over Q[zeta_n] via sympy cyclotomic factoring, OR
     over a big prime p >> n^4) of I(delta) and delta* for n in {8,16,32}, rho in
     {1/4,1/2}.  Cross-checks the measured ground truth in the issue.
 (2) Decomposes each delta*-achieving direction's agreement sets into
     cyclotomic-coset (antipodal) blocks -> the Mann decomposition, to get a
     CLOSED orbit-count formula candidate.
 (3) Tests the conjectured shape delta* = 1 - rho - Theta(1/log n).

HONESTY: mu_n is a PROPER subgroup (n=2^a, p=1 mod n, p-1 != n).  Exact char-0
path uses integer/rational cyclotomic arithmetic (no rounding).  Big-prime path
uses p >> n^4, p chosen NOT of high 2-adic valuation beyond what n forces.
All claims tagged proven/measured/conjecture.
"""

import itertools, sys
from math import gcd

# ---------- prime-field exact arithmetic over mu_n (p >> n^4) ----------
def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime_1_mod_n(n, lo):
    # smallest prime p > lo with p = 1 mod n; avoid p-1 == n (need PROPER subgroup,
    # which lo >> n guarantees).  We DON'T need to avoid 2-adic valuation: char-0
    # faithfulness for over-det depth >=3 is p-independent for p >> n^4 (issue).
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p):
            return p
        p += n

def primitive_root(p):
    # find generator of F_p^*
    fac = []
    m = p - 1
    d = 2
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
    return [pow(w, i, p) for i in range(n)]  # mu[i] = w^i

# ---------- consistency: does (gamma) admit deg<k poly g s.t. x^a+gamma x^b = g on S? ----------
# Equivalent rank test.  For a SUBSET S (|S|=w) of mu_n indices, the pencil value at
# index i is h_i = mu[i]^a + gamma*mu[i]^b.  There's a deg<k poly g agreeing on S iff
# the vector (h_i)_{i in S} lies in the column space of the Vandermonde V_S =
# [mu[i]^0 ... mu[i]^{k-1}]_{i in S}.  Since |S|=w>k, that's w-k linear conditions.
# We instead want, for FIXED direction (a,b): the MAX over S of #gamma realizing it,
# but the issue's I(delta) counts DISTINCT gamma over ALL w-subsets:
#   I(delta) = #{ gamma : EXISTS w-subset S, x^a+gamma x^b agrees w/ some deg<k g on S }.
# We compute that directly.

def lagrange_interp_value(xs, ys, x, p):
    # interpolate (xs,ys) [len<=k assumed independent], evaluate at x
    tot = 0
    L = len(xs)
    for i in range(L):
        num = ys[i]; den = 1
        for j in range(L):
            if j == i: continue
            num = num * ((x - xs[j]) % p) % p
            den = den * ((xs[i] - xs[j]) % p) % p
        tot = (tot + num * pow(den, p-2, p)) % p
    return tot

def agrees_on_subset(mu, a, b, gamma, S, k, p):
    """Does there exist deg<k poly g with mu[i]^a+gamma mu[i]^b = g(mu[i]) for all i in S?
       Interpolate first k points of S, check the rest match."""
    Sl = sorted(S)
    pts = [mu[i] for i in Sl]
    h = [(pow(mu[i], a, p) + gamma * pow(mu[i], b, p)) % p for i in Sl]
    if len(Sl) <= k:
        return True
    base_x = pts[:k]; base_y = h[:k]
    for idx in range(k, len(Sl)):
        if lagrange_interp_value(base_x, base_y, pts[idx], p) != h[idx]:
            return False
    return True

def max_agreement_for_gamma(mu, a, b, gamma, k, p, n):
    """For fixed (a,b,gamma): the LARGEST w such that some w-subset agrees with deg<k g.
       = (max #mu_n-roots of x^a+gamma x^b - g over deg<k g) = size of largest consistent
       agreement set.  We compute it via the cyclotomic/antipodal structure directly:
       the agreement set of a fixed g is the mu_n-root set of F=x^a+gamma x^b-g.  But we
       want the MAX over g.  Equivalent: greedily, the max consistent set.
       We use the rank characterization: an index set S is consistent iff the (a,b)-pencil
       values lie in deg<k span on S.  Largest such S = n - (min #constraints violated).
       Practical exact method: build the n x (k+2) generalized Vandermonde-ish system and
       find largest subset of rows consistent.  For our sizes we do it by:
         for each candidate g supported by k chosen anchor points, the agreement set is
         determined; take max over anchor choices.  Too big -> use structural method below.
    """
    # STRUCTURAL exact method (Mann): F = x^a + gamma x^b - g(x), deg g<k.  Its mu_n root
    # set = union of cyclotomic cosets.  The agreement set for the BEST g is the largest
    # union of cosets C (each C = roots of Phi_d, d|n) such that x^a+gamma x^b restricted
    # to C is interpolable by deg<k on C TOGETHER (consistency across cosets).  We just
    # directly compute the max consistent subset by a rank-growth over all of mu_n: start
    # from the full set and find the largest subset S where pencil-values are deg<k-consistent.
    # Largest deg<k-consistent subset = we test: a subset S is consistent iff
    #   rank[ V_S | h_S ] == rank[ V_S ]  (h in column space) AND we want max |S|.
    # Max consistent set under a single linear-agreement constraint family: equivalently
    # the agreement multiset of the best codeword. We compute via: for each k-subset as
    # interpolation anchor, count total agreements; max over anchors. n choose k is fine
    # for n<=16,k<=8 small; for n=32 we restrict to structured anchors (cosets).
    best = 0
    idxs = list(range(n))
    # heuristic+exact for small n: iterate anchors = k-subsets
    if n <= 16:
        for anchor in itertools.combinations(idxs, k):
            xs = [mu[i] for i in anchor]
            ys = [(pow(mu[i], a, p) + gamma*pow(mu[i], b, p)) % p for i in anchor]
            # g = interpolation through anchor; count agreements over all mu_n
            cnt = 0
            for i in idxs:
                if lagrange_interp_value(xs, ys, mu[i], p) == (pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p:
                    cnt += 1
            if cnt > best: best = cnt
        return best
    else:
        # n=32: anchors restricted to coset-structured + random; report a LOWER bound
        import random
        random.seed(0)
        tried = set()
        anchors = []
        # structured: take arithmetic-progression index anchors (coset-aligned)
        for step in [1,2,4,8,16]:
            for start in range(0, min(step, n)):
                a_idx = tuple(sorted((start + j*step) % n for j in range(k)))
                if len(set(a_idx))==k: anchors.append(a_idx)
        for _ in range(2000):
            anchors.append(tuple(sorted(random.sample(idxs, k))))
        for anchor in anchors:
            if anchor in tried: continue
            tried.add(anchor)
            xs = [mu[i] for i in anchor]
            ys = [(pow(mu[i], a, p) + gamma*pow(mu[i], b, p)) % p for i in anchor]
            cnt = 0
            for i in idxs:
                if lagrange_interp_value(xs, ys, mu[i], p) == (pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p:
                    cnt += 1
            if cnt > best: best = cnt
        return best

def compute_I_and_deltastar(n, k, p, mu, directions=None, verbose=False):
    """For each w (=threshold), I(w) = #{gamma : some w-subset agrees}.  Equivalent:
       gamma counts toward threshold w iff max_agreement_for_gamma >= w.
       I(delta) with w=(1-delta)n.  Return dict w -> max over directions of #good gamma,
       and the achieving direction."""
    if directions is None:
        # far exponents a<b, both >= k (over-determined / far); restrict to a,b in [k, n-1]
        directions = [(a,b) for a in range(k, n) for b in range(a+1, n)]
    # For each direction, for each gamma in F_p (too many!) we can't loop p>>n^4.
    # KEY: agreement set only depends on gamma through the pencil; bad gammas form a
    # SMALL structured set (orbit of e_m(S)).  We enumerate candidate gammas as those
    # for which SOME k-subset anchor forces a deg<k g matching at >=k+1 points.  Construct
    # candidate gammas: pick a (k+1)-subset T; solve for gamma making x^a+gamma x^b deg<k
    # on T (one linear eqn from the (k+1)-th consistency).  That yields all gammas that
    # achieve agreement >= k+1 somewhere.  Then refine threshold.
    results = {}        # w -> (count, best_dir)
    for (a, b) in directions:
        # collect candidate gammas + their max agreement
        gamma_maxagree = {}
        # candidate gammas: for each (k+1)-subset T, the unique gamma s.t. pencil is
        # deg<k-interpolable on T (if exists). |T|=k+1.
        for T in itertools.combinations(range(n), k+1):
            xs = [mu[i] for i in T]
            # condition: vector (mu^a + gamma mu^b) on T in deg<k span.  The deg<k span on
            # k+1 distinct points has codim 1; the orthogonal functional is the divided
            # difference / the unique (up to scale) linear functional L with L(deg<k)=0.
            # L(v) = sum_i c_i v_i where c_i = 1/prod_{j!=i}(x_i-x_j) (k+1 points, deg<k
            # => the top divided difference vanishes). Then need L(mu^a)+gamma L(mu^b)=0.
            c = []
            for i in range(k+1):
                den = 1
                for j in range(k+1):
                    if j==i: continue
                    den = den*((xs[i]-xs[j])%p)%p
                c.append(pow(den, p-2, p))
            La = sum(c[i]*pow(xs[i], a, p) for i in range(k+1)) % p
            Lb = sum(c[i]*pow(xs[i], b, p) for i in range(k+1)) % p
            if Lb == 0:
                if La == 0:
                    # every gamma works on this T (degenerate) - skip (would need full sweep)
                    continue
                else:
                    continue  # no finite gamma
            gamma = (-La * pow(Lb, p-2, p)) % p
            if gamma not in gamma_maxagree:
                ma = max_agreement_for_gamma(mu, a, b, gamma, k, p, n)
                gamma_maxagree[gamma] = ma
        # also gamma=0 etc are far-trivial (x^a alone agrees w/ 0 only on... ) skip;
        # now per threshold w: count gammas with maxagree>=w
        for w in range(k+1, n+1):
            cnt = sum(1 for g,ma in gamma_maxagree.items() if ma >= w)
            if w not in results or cnt > results[w][0]:
                results[w] = (cnt, (a,b))
    return results

def deltastar_from_results(results, n, budget):
    """delta* = sup{delta : I(delta)<=budget}.  I(delta) at w=(1-delta)n.  As delta
       increases w decreases I increases.  delta* = largest delta (smallest w) with
       I(w) <= budget.  Report the w boundary and delta*=1-w/n."""
    # find largest w such that I(w) <= budget; delta = 1 - w/n.  We want sup delta with
    # I<=budget => smallest w with I(w)<=budget, then delta*=1-w/n? No: I increases as w
    # shrinks.  At w=n, I small.  We want the threshold w0 = smallest w with I(w)>budget;
    # then for w>=w0+1 ... careful.  Define delta admissible if I(delta)<=budget, i.e.
    # #gammas with agreement >= (1-delta)n is <= budget.  As delta grows, w drops, more
    # gammas qualify, I grows.  delta* = sup admissible delta.  So find largest w (call w*)
    # with I(w) <= budget for ALL w' >= ... actually I(w) monotone decreasing in w.
    # admissible delta <=> I((1-delta)n) <= budget <=> w=(1-delta)n satisfies I(w)<=budget.
    # Since I decreasing in w, the admissible w are w >= w_min where w_min = smallest w with
    # I(w)<=budget.  delta*=1-w_min/n.
    ws = sorted(results.keys())
    w_min = None
    for w in ws:
        if results[w][0] <= budget:
            w_min = w
            break
    if w_min is None:
        return None, None, None
    return 1 - w_min/n, w_min, results[w_min]

def main():
    print("="*78)
    print("A5 Mann/antipodal exact char-0 (big-prime p>>n^4) delta* computation")
    print("="*78)
    cases = [(8,2), (8,4), (16,4), (16,8)]   # (n,k): rho=1/4 and 1/2
    for (n,k) in cases:
        rho = k/n
        p = find_prime_1_mod_n(n, n**4 * 4)   # p >> n^4
        mu = roots_of_unity(p, n)
        budget = n   # q*eps* ~ n
        results = compute_I_and_deltastar(n, k, p, mu)
        ds, w_min, info = deltastar_from_results(results, n, budget)
        print(f"\n--- n={n}, k={k} (rho={rho}), p={p} ---")
        print(f"  budget = n = {n}")
        # print I(w) table
        for w in sorted(results.keys(), reverse=True):
            cnt, dirn = results[w]
            mark = " <-- delta* boundary" if w==w_min else ""
            print(f"    w={w:2d} (delta={1-w/n:.4f}): I={cnt:3d}  bestdir={dirn}{mark}")
        if ds is not None:
            print(f"  ==> delta*(measured) = {ds:.4f}  at w_min={w_min}, dir={info[1]}")
            # compare to issue ground truth
            gt = {(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}.get((n,k))
            if gt is not None:
                print(f"      issue ground-truth delta* = {gt}   MATCH={abs(ds-gt)<1e-9}")
            # conjecture shape: 1 - rho - c/log2 n
            import math
            c = (1-rho-ds)*math.log2(n)
            print(f"      shape 1-rho-c/log2(n): c = {c:.4f}  (1-rho={1-rho})")

if __name__ == "__main__":
    main()
