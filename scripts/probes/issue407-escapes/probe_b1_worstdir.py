#!/usr/bin/env python3
"""
ESCAPE B1 exact numerics — worst-direction agreement-set size |S| for monomial lines.

Setup (prize regime model, scaled down):
  - mu_n = <g> the n-th roots of unity in F_p, p prime, p == 1 mod n, m=(p-1)/n.
  - Monomial line word: w(x) = x^a + gamma * x^b  for x in mu_n  (a > b WLOG via degree).
  - Codeword: c = eval(P), deg P < k  (RS[k]).
  - Agreement set S = { x in mu_n : w(x) == c(x) }.
  - The agreement polynomial is  Q(x) = x^a + gamma*x^b - P(x), (k+2)-sparse, |S| = #roots in mu_n.
  - Direction d = gcd(a-b, n). Far iff dist > witness budget. Kambire worst d ~ n/44.

KEY QUESTION (comment 125 vs 100, 142):
  Does the SINGLE-poly realizability constraint (S = roots of ONE deg-<k poly P, not arbitrary)
  reduce max |S| below the generic root-count budget?

We measure, for each direction (a,b) and each radius w (=agreement count threshold):
  N_bad(w) = #{ gamma in F_p* : exists deg-<k P with |{x in mu_n: x^a+gamma x^b = P(x)}| >= w }
  and  maxS(a,b,gamma) over gamma = the largest agreement set achievable.

To find the MAX agreement set for a given (a,b,gamma): the largest set S of mu_n points on which
x^a+gamma x^b equals SOME deg-<k poly = the largest subset of size>=k+1 whose values
(x_i, x_i^a+gamma x_i^b) lie on a common deg-<k poly... but any k points lie on a deg-<k poly.
The realizability constraint is: a set S of size s is realizable iff the unique deg-<? interpolant
through ALL points of S that has degree < k. I.e. S realizable as agreement set of deg-<k codeword
iff the (k+2)-sparse poly  x^a+gamma x^b - P  vanishes on S for some deg-<k P, i.e. the
divided differences / the values {(x, x^a+gamma x^b): x in S} are interpolated by a deg-<k poly.

s points lie on a deg-<k poly iff all order-k divided differences of the function f(x)=x^a+gamma x^b
over those s points vanish. For s <= k that's automatic. For s > k it is s-k linear constraints on gamma
(given the point set). The MAX over gamma and over point-sets is what we want.

We do it EXACTLY by, for each candidate point subset structure, but that's exponential. Instead we use
the algebraic fact:  S is an agreement set of a deg-<k codeword  iff  there is a deg-<k P with
x^a+gamma x^b - P vanishing on S, iff  prod_{x in S}(X-x)  divides  some (k+2)-sparse poly with
top terms x^a+gamma x^b. Equivalently the polynomial  R_S(X) = x^a+gamma x^b mod prod_{x in S}(X-x)
has degree < k. So: |S| achievable  <=>  (x^a + gamma x^b) reduced mod (prod_{x in S}(X-x)) has deg<k.

For the MAX agreement set: we want the largest S subset of mu_n s.t. the remainder of x^a+gamma x^b
mod prod_{S}(X-x) has degree < k. We compute this directly by Reed-Solomon / interpolation:
given gamma, the codeword that best agrees = the deg-<k poly minimizing disagreements. We just
enumerate: for each x in mu_n compute f(x)=x^a+gamma x^b, then the agreement set of a SPECIFIC P
is {x: P(x)=f(x)}. The max-agreement P is the one whose graph passes through the most (x,f(x)) pairs
that lie on a deg-<k curve. We find max agreement = n - min Hamming distance from f to RS[k].
"""
import itertools, math
from sympy import isprime

def find_prime(n, want_min):
    # smallest prime p == 1 mod n with p >= want_min
    p = max(want_min, n+1)
    if p % n != 1:
        p += (1 - p % n) % n
    while True:
        if p % n == 1 and isprime(p):
            return p
        p += n

def primitive_nth_root(p, n):
    # find g with order exactly n in F_p^*. Take a generator^((p-1)/n).
    # find a multiplicative generator (small search)
    from sympy import factorint
    fac = list(factorint(p-1).keys())
    for cand in range(2, p):
        if all(pow(cand,(p-1)//q,p)!=1 for q in fac):
            g0 = cand; break
    w = pow(g0, (p-1)//n, p)
    return w

def mu_n(p,n):
    w = primitive_nth_root(p,n)
    return [pow(w, j, p) for j in range(n)], w

def rs_min_distance_to(f_vals, xs, k, p):
    """min Hamming distance from word f to RS[k] over eval points xs (size n).
       = n - max agreement = n - (largest #points on a common deg-<k poly).
       Exact via: max agreement set = max over deg-<k polys of #{f(x)=P(x)}.
       We compute by brute: for every (k)-subset choose interpolant? expensive.
       Instead use the fact that max agreement of an RS[k] code with received word
       = n - dmin(received, code). Brute force over all deg-<k polys is p^k. Too big.
       Use list-decoding-free exact: agreement count for poly P = #{x: P(x)=f(x)}.
       The optimal P interpolates SOME k of the agreement points. So max agreement
       = max over k-subsets T of xs of (#points where the interpolant of (T,f|T) equals f).
       That is C(n,k) interpolations — feasible for small n,k."""
    n = len(xs)
    best = 0
    idx = list(range(n))
    # precompute f at each
    for T in itertools.combinations(idx, k):
        # interpolate deg<k poly through (xs[t], f_vals[t]) for t in T (k points -> unique deg<k)
        # then count agreements
        # Lagrange evaluate at all xs
        agree = 0
        # Build interpolation: we evaluate P at each x_j via Lagrange over T
        for j in idx:
            xj = xs[j]; num = 0
            # Lagrange: P(xj) = sum_{t in T} f[t] * prod_{s in T, s!=t} (xj - xs[s])/(xs[t]-xs[s])
            val = 0
            for t in T:
                term = f_vals[t] % p
                xt = xs[t]
                for s in T:
                    if s==t: continue
                    xs_s = xs[s]
                    term = (term * ((xj - xs_s) % p)) % p
                    inv = pow((xt - xs_s) % p, p-2, p)
                    term = (term * inv) % p
                val = (val + term) % p
            if val == f_vals[j] % p:
                agree += 1
        if agree > best:
            best = agree
            if best == n: break
    return n - best, best

def main():
    print("="*100)
    print("B1 worst-direction: max agreement |S| of monomial line x^a+gamma x^b with RS[k] over mu_n")
    print("="*100)
    # small enough to brute: n=8,12,16 with small k
    for n in [8, 12, 16]:
        # prize-ish: pick a prime; sweep a few gamma; compare maxS vs sqrt(n*k), Johnson, deg b
        p = find_prime(n, n*40+1)   # index m~40 (toy "constant index")
        xs, w = mu_n(p, n)
        m = (p-1)//n
        print(f"\n--- n={n}, p={p} (m=(p-1)/n={m}) ---")
        ks = sorted(set([2, max(2,n//4), max(2,n//2)]))
        for k in ks:
            rho = k/n
            sqrtnk = math.sqrt(n*k)
            johnson = n*(1-math.sqrt(rho))   # Johnson list-decoding agreement radius ~ sqrt(rho)n agreement => far below
            # sweep directions: a>b, d=gcd(a-b,n). Focus on a in [k, n-1], b in [0, a-1].
            # For each (a,b) sweep gamma over F_p*, find max agreement over gamma.
            rows = []
            for a in range(k, n):          # a >= k (else x^a is itself a codeword)
                for b in range(0, a):
                    d = math.gcd(a-b, n)
                    # sweep gamma (sample if p large)
                    gammas = range(1, p)
                    if p > 200:
                        # sample
                        step = max(1, (p-1)//150)
                        gammas = range(1, p, step)
                    bestS = 0; bestg = None
                    for g in gammas:
                        fvals = [(pow(xs[i], a, p) + g*pow(xs[i], b, p)) % p for i in range(n)]
                        dist, agree = rs_min_distance_to(fvals, xs, k, p)
                        if agree > bestS:
                            bestS = agree; bestg = g
                    rows.append((a,b,d,bestS,bestg))
            # report the worst (max) agreement direction
            rows.sort(key=lambda r:-r[3])
            top = rows[0]
            print(f"  k={k} rho={rho:.3f}  sqrt(nk)={sqrtnk:.2f}  | WORST dir a={top[0]} b={top[1]} d={top[2]}: maxS={top[3]} (gamma={top[4]})")
            # show distribution by direction d
            bydir = {}
            for (a,b,d,s,g) in rows:
                bydir.setdefault(d, []).append(s)
            dline = "    by d: " + "  ".join(f"d={d}:max{max(v)}" for d,v in sorted(bydir.items()))
            print(dline)

if __name__=="__main__":
    main()
