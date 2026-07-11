#!/usr/bin/env python3
"""
probe_407_e2_census_K_n64.py  (#444 — the load-bearing e2=0 census R1 lane, n=64 growth law)

CONTEXT: _E2DilationDirectCount.lean exposes the prize FLOOR's Attack-2 residual as the e2=0
extremal orbit census K(n): #{bad alpha} = n*K, K = #dilation-orbits (under mu_n) of e1(S) over
{S subset mu_n, |S|=w=n/2, e2(S)=0, e1(S)!=0}. In-tree K=1,3,38 at n=8,16,32. The file itself
states K is "super-linear; the count does NOT collapse to O(n)" — but only has 3 points.

THE BUDGET FACT (governing law, KB deltastar-orbit-count-reformulation): delta* = sup{delta:
I(delta) <= q*eps* ~= n}. So the e2=0 family is WITHIN the floor budget iff #bad = n*K <= n,
i.e. iff K <= 1. K=1,3,38 already VIOLATES this for n>=16. The decisive open question: the
GROWTH LAW of K(n). 3->12.67x ratio (n8->16->32) suggests super-polynomial. n=64 settles it.

METHOD: 4-way meet-in-the-middle. Split mu_64 into 4 quarters Q0..Q3 of 16 each. For width w=32,
enumerate (k0,k1,k2,k3) with sum=32; for each quarter enumerate all k_i-subsets -> (s1,s2) partial
power-sums. Combine Q0+Q1 -> dict keyed by (s1,s2); Q2+Q3 -> need (s1,s2) s.t. total
(S1)^2 == S2 mod p, S1 != 0. Hash-join on the linear constraint: for fixed left (a1,a2), need
right (b1,b2) with (a1+b1)^2 == a2+b2  <=>  b2 == (a1+b1)^2 - a2  (1 eqn, 2 unknowns -> for each
right b1, the required b2 is determined; build right index keyed by (b1, b2)). To keep it exact +
feasible, we index the RIGHT side by b1 -> list of (b2 multiset counts) and for each LEFT (a1,a2)
and each candidate total S1, look up. Simplest exact approach within RAM: index right by
(b1 mod p) into a dict of Counter(b2); for each left and each right-b1 value, compute required
b2=(a1+b1)^2-a2 and add the count. We collect the resulting e1 = S1 values (a1+b1) into a set, then
orbit-reduce under mu_64. p = n^4 prize prime (+ a second prime for q-invariance).

Feasibility: each quarter C(16,k) <= 12870; pairwise (Q0xQ1) products are <= sum_k C(16,k)C(16,32-...)
bounded; the join is over distinct b1 values (<= p but in practice the realized set). Exact, no
sampling.
"""
import itertools, math, time, sys
from collections import defaultdict, Counter

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def prize_prime(n, beta=4):
    p = n**beta
    p -= p % n; p += 1
    while not ((p-1) % n == 0 and isprime(p)): p += n
    return p

def factor(x):
    f=[]; d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: f.append(x)
    return f

def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 0

def quarter_partials(qroots, p):
    """For a quarter (list of roots), return dict: k -> list of (s1,s2) over all k-subsets."""
    h = len(qroots)
    out = {}
    for k in range(h+1):
        lst = []
        for c in itertools.combinations(range(h), k):
            s1=0; s2=0
            for i in c:
                v=qroots[i]; s1+=v; s2+=v*v
            lst.append((s1 % p, s2 % p))
        out[k] = lst
    return out

def combine_two(pa, pb, p, kmax):
    """Combine two quarters' partials into dict: ktot -> dict keyed (s1,s2) -> count.
    Only keep ktot up to kmax (=w). Returns {ktot: Counter((s1,s2))}."""
    res = {}
    for ka, la in pa.items():
        for kb, lb in pb.items():
            kt = ka+kb
            if kt > kmax: continue
            c = res.setdefault(kt, Counter())
            for (a1,a2) in la:
                for (b1,b2) in lb:
                    c[((a1+b1) % p, (a2+b2) % p)] += 1
    return res

def e2_census_n64(n, p, verbose=True):
    g = pow(proot(p), (p-1)//n, p)
    mu = [pow(g, j, p) for j in range(n)]
    assert pow(mu[1], n, p) == 1 and pow(mu[1], n//2, p) != 1
    w = n//2
    q = n//4
    Q = [mu[0:q], mu[q:2*q], mu[2*q:3*q], mu[3*q:4*q]]
    t0=time.time()
    parts = [quarter_partials(Qi, p) for Qi in Q]
    if verbose: print(f"  quarter partials done {time.time()-t0:.1f}s", flush=True)
    # left = Q0+Q1, right = Q2+Q3
    left = combine_two(parts[0], parts[1], p, w)
    if verbose: print(f"  left combine done {time.time()-t0:.1f}s ktots={sorted(left)}", flush=True)
    right = combine_two(parts[2], parts[3], p, w)
    if verbose: print(f"  right combine done {time.time()-t0:.1f}s ktots={sorted(right)}", flush=True)
    # build right index: for each kR, group by b1 -> Counter(b2)
    e1set = set()
    nbad = 0
    for kL, cL in left.items():
        kR = w - kL
        if kR not in right: continue
        cR = right[kR]
        # index right by b1 -> Counter of b2
        idx = defaultdict(Counter)
        for (b1,b2), cnt in cR.items():
            idx[b1][b2] += cnt
        b1_keys = list(idx.keys())
        for (a1,a2), cntL in cL.items():
            for b1 in b1_keys:
                S1 = (a1 + b1) % p
                if S1 == 0: continue
                need_b2 = (S1*S1 - a2) % p
                c2 = idx[b1].get(need_b2)
                if c2:
                    nbad += cntL * c2
                    e1set.add(S1)
        if verbose: print(f"    kL={kL} kR={kR} cumulative #distinct-e1={len(e1set)} nbad={nbad} t={time.time()-t0:.1f}s", flush=True)
    # orbit-reduce under mu
    rem = set(e1set); K=0; muset=mu
    while rem:
        x=next(iter(rem)); rem -= set((u*x)%p for u in muset); K+=1
    return nbad, len(e1set), K

def main():
    n = 64
    print(f"=== e2=0 census K({n}) — 4-way MITM, w={n//2}, prize prime ===", flush=True)
    for beta, tag in [(4,"beta4"), (4,"beta4-2nd")]:
        p = prize_prime(n, beta)
        if tag.endswith("2nd"):
            # next prize prime for q-invariance
            p2 = p + n
            while not isprime(p2): p2 += n
            p = p2
        print(f"\n--- n={n} p={p} ({tag}) p/n^3={p/n**3:.1f} ---", flush=True)
        nbad, dist, K = e2_census_n64(n, p)
        print(f"  RESULT n={n}: #bad-sets/distinct-e1={dist}  K(orbits)={K}  #bad=n*K? n*K={n*K}", flush=True)
        print(f"  K({n})={K}  | in-tree K(8,16,32)=1,3,38  | budget closes iff K<=1", flush=True)

if __name__ == "__main__":
    main()
