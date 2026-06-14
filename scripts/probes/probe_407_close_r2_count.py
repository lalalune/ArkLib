"""
R2a (efficient): at FIXED radius delta, which (s|n, r) maximizes the distinct-r-fold-sumset
count |H^{(+r)}(mu_s)|?  Use FFT-free exact integer enumeration over the cyclotomic ring
Z[zeta_s] with the integral basis (deg phi(s)), so sums are exact lattice points.

For s = 2^a, zeta = primitive s-th root, integral basis {1,zeta,...,zeta^{s/2-1}} (since zeta^{s/2}=-1).
Each s-th root zeta^t (0<=t<s) is +-zeta^{t mod s/2}.  So a sum of r distinct roots is an exact
integer vector of length s/2.  Enumerate distinct sums by DP over the s roots (subset-sum with
exactly r picks), tracking the set of reachable integer vectors.  Feasible for s up to ~24.
"""
import math
from math import comb
from itertools import combinations

def root_vec(s, t):
    """Integer vector (length s/2) for zeta_s^t in basis {1,...,zeta^{s/2-1}}, zeta^{s/2}=-1."""
    h = s//2
    v = [0]*h
    tt = t % s
    if tt < h:
        v[tt] = 1
    else:
        v[tt-h] = -1
    return tuple(v)

def distinct_rfold_sumset_count(s, r):
    """Exact distinct count of sums of r distinct s-th roots (char 0), s a power of 2."""
    if r < 0 or r > s: return 0
    h = s//2
    rvs = [root_vec(s,t) for t in range(s)]
    # DP: dp[j] = set of reachable vectors using exactly j roots, picking from a prefix.
    # Use standard 0/1 knapsack with exactly-r constraint over s items.
    from functools import lru_cache
    # iterative: layers
    dp = [set() for _ in range(r+1)]
    dp[0].add(tuple([0]*h))
    for t in range(s):
        rv = rvs[t]
        for j in range(min(r, t+1), 0, -1):
            newset = dp[j]
            for vec in dp[j-1]:
                nv = tuple(vec[i]+rv[i] for i in range(h))
                newset.add(nv)
    return len(dp[r])

print("="*92)
print("R2a: at FIXED delta, which (s|n,r) MAXIMIZES distinct-r-fold-sumset |H^{(+r)}(mu_s)|?")
print("(Kambire uses s=2^alpha = the LARGEST subgroup realizing the radius. Test if that maximizes.)")
print("="*92)
for mu in [5,6,7]:
    n = 2**mu
    print(f"\n--- n=2^{mu}={n} ---")
    for target_delta in [0.5, 0.625, 0.75, 0.8125]:
        rows=[]
        for a in range(2, mu+1):
            s = 2**a
            r_exact = (1-target_delta)*s
            if abs(r_exact-round(r_exact))>1e-9: continue
            r = round(r_exact)
            if not (1<=r<=s//2): continue   # r<=s/2 for the antipodal-free count to be meaningful
            if s>24 and (comb(s,r) > 5_000_000): 
                rows.append((s,r,"(skipped, too big)")); continue
            cnt = distinct_rfold_sumset_count(s,r)
            rows.append((s,r,cnt))
        if not rows: continue
        numeric = [x for x in rows if isinstance(x[2],int)]
        best = max(numeric, key=lambda x:x[2]) if numeric else None
        print(f"  delta={target_delta}:  " + "  ".join(f"s={s},r={r}->{c}" for (s,r,c) in rows)
              + (f"   MAX: s={best[0]},r={best[1]}={best[2]}" if best else ""))
