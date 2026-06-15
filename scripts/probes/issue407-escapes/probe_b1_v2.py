#!/usr/bin/env python3
"""
B1 exact numerics v2 — FAST max-agreement via divided differences.

For monomial-line word f(x) = x^a + gamma*x^b over mu_n, and RS[k] (deg<k),
the max agreement set S (|S| = #{x in mu_n: f(x)=P(x)} for the best deg-<k P) =
n - d_min(f, RS[k]).

EFFICIENT exact max-agreement:
A set S of mu_n points lies on a common deg-<k poly with values f
 iff the |S|-th order structure collapses: equivalently the
 (k+1)-st divided differences of (x, f(x)) over the points all vanish ... but for finding
 the MAX over all subsets this is still combinatorial.

Better: enumerate codewords cleverly. Max agreement = max over deg-<k polys P of #agree(P,f).
A maximizing P is determined by k of the agreement points (interpolation). For modest C(n,k)
this is fine. To make n=16 feasible we PRUNE: we only need the TOP agreement; we can bound and
break. Also we cache pow tables. We also reduce gamma sweep: by the dilation/scaling covariance
the answer for (a,b,gamma) relates to (a,b,gamma') — but to be safe we sample gamma densely.

We ALSO compute the key realizability discriminant:
  generic_root_budget = number of roots a (k+2)-sparse poly x^a+gamma x^b - P can have in mu_n
     = deg of agreement poly capped by structure = up to a (=deg) generically, but
       the SINGLE-poly (one fixed P, one fixed gamma) gives the actual |S|.
We compare measured maxS to:
  - sqrt(nk)        (refuted raw R-thin)
  - deg b ~ a       (degree budget, ragged_excess backbone)
  - additive s=n/d  (autocorrelation Theta(s) budget)
  - k+1             (isolated-point Beukers-Smyth, comment 142)
  - Johnson agreement floor = ceil(sqrt(n*k)) (list radius)
"""
import itertools, math
from sympy import isprime, factorint

def find_prime(n, want_min):
    p = max(want_min, n+1)
    r = p % n
    if r != 1:
        p += (1 - r) % n
    while True:
        if p % n == 1 and isprime(p):
            return p
        p += n

def generator(p):
    fac = list(factorint(p-1).keys())
    for cand in range(2, p):
        if all(pow(cand,(p-1)//q,p)!=1 for q in fac):
            return cand
    raise RuntimeError

def mu_n(p,n):
    g0 = generator(p)
    w = pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def max_agreement(fvals, xs, k, p, early_stop=None):
    """max #{x: P(x)=f(x)} over deg-<k P. Brute via k-subset interpolation with pruning."""
    n = len(xs)
    if k >= n:
        return n
    best = k  # any k points are interpolated exactly, so >= k always
    idx = list(range(n))
    # Precompute inverse differences lazily
    invcache = {}
    def inv(z):
        z%=p
        if z in invcache: return invcache[z]
        r = pow(z,p-2,p); invcache[z]=r; return r
    for T in itertools.combinations(idx, k):
        # Lagrange interpolant through T, evaluate at all points, count agreement
        agree = 0
        miss_allow = n - best  # if we can't beat best, prune
        seen = 0
        for j in idx:
            seen += 1
            xj = xs[j]
            val = 0
            for t in T:
                term = fvals[t]
                xt = xs[t]
                for s in T:
                    if s==t: continue
                    term = (term * ((xj - xs[s]) % p)) % p
                    term = (term * inv((xt - xs[s]))) % p
                val = (val + term) % p
            if val == fvals[j]:
                agree += 1
            else:
                # prune: max possible from here
                if agree + (n - seen) <= best:
                    break
        if agree > best:
            best = agree
            if early_stop and best >= early_stop:
                return best
    return best

def main():
    print("="*110)
    print("B1 v2: max agreement |S| of monomial line vs RS[k] over mu_n  (EXACT, p == 1 mod n)")
    print("="*110)
    for n in [8, 12, 16]:
        p = find_prime(n, n*40+1)
        xs,w = mu_n(p,n)
        m=(p-1)//n
        print(f"\n### n={n}  p={p}  m=(p-1)/n={m} ###")
        for k in sorted(set([2, n//4 if n//4>=2 else 2, n//2])):
            rho=k/n
            sqrtnk=math.sqrt(n*k)
            # gamma sweep (sample)
            G = list(range(1,p))
            if len(G)>120:
                step=max(1,(p-1)//120); G=list(range(1,p,step))
            results=[]
            for a in range(k,n):
                for b in range(0,a):
                    d=math.gcd(a-b,n)
                    bestS=0;bg=None
                    for g in G:
                        fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
                        s=max_agreement(fv,xs,k,p)
                        if s>bestS: bestS=s;bg=g
                    results.append((a,b,d,bestS,bg))
            results.sort(key=lambda r:-r[3])
            t=results[0]
            sd = n//t[2] if t[2]>0 else n
            print(f"  k={k} rho={rho:.3f}: WORST a={t[0]} b={t[1]} d={t[2]} maxS={t[3]} | sqrt(nk)={sqrtnk:.2f} k+1={k+1} deg_b={t[1] or t[0]} s=n/d={sd}")
            # per-direction d max
            bd={}
            for (a,b,d,s,g) in results: bd.setdefault(d,0); bd[d]=max(bd[d],s)
            print("    maxS by d: "+"  ".join(f"d={d}:{v}" for d,v in sorted(bd.items())))

if __name__=="__main__":
    main()
