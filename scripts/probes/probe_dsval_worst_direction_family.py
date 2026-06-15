#!/usr/bin/env python3
"""
#407 / A3 WORST-DIRECTION FAMILY.

Question: among all far monomial directions (a,b), k<=a<b<n, WHICH maximizes the over-determined
far-line incidence I(a,b; delta) at the BINDING band, and is there a closed-form family?

Setup (faithful per the contract):
  - mu_n = full multiplicative subgroup of order n=2^a, a PROPER subgroup (n | q-1, n != q-1).
  - char-0 == big prime q >> n^4 (over-det band is p-independent). We pick q a prime with q-1
    divisible by n, q > n^4, AVOIDING Fermat / high-2-adic-valuation artifacts: we require
    v2(q-1) == v2(n) exactly (smallest legal 2-adic valuation), so mu_n is the unique 2-power
    subgroup and there is no extra 2-torsion to create spurious agreement.
  - incidence I(a,b; w): number of distinct gamma in F_q s.t. x^a + gamma*x^b agrees with SOME
    poly of deg<k on a w-subset of mu_n. Computed exactly: for every (n-w)-subset that the line
    must MISS... no -- we iterate over the COMPLEMENT. A w-subset agreement <=> the s=n-w deleted
    points; we iterate over all w-subsets W, build generalized-Vandermonde rank test.

  We use the difference-quotient / consistency formulation from the existing ground-truth probe:
  for a candidate w-subset W (|W|=w), the values (x^a + gamma x^b)_{x in W} lie in deg<k space
  iff all order-k divided differences vanish. Linear in gamma: a0_J + gamma*a1_J = 0 for each
  k-window J in W (after ordering). gamma exists (a single value) iff the system is consistent
  (all ratios equal); we collect that gamma. I = #distinct gammas over all w-subsets.

  budget = n. delta*(n,rho) = max{ delta=1-w/n : I_worstdir(w) <= n }, i.e. smallest w (deepest
  band) with worst-direction incidence still <= budget; report 1 - (that w)/n? NO -- delta grows
  as w shrinks; we want sup delta with I<=n, = 1 - w_min/n where w_min is the SMALLEST w whose
  worst-dir incidence is still <= n... incidence is INCREASING as w DECREASES (more subsets, more
  freedom). So I<=n holds for LARGE w (shallow), fails for small w. delta* = 1 - w*/n where w* is
  the smallest w with I(w) <= n. Equivalent to existing probe's "first w from k+1 up with I<=n".

We report, for each (n,k): the worst direction(s) achieving max incidence at the binding band,
their invariants d=gcd(b-a,n), a, b, b-a, and a-k, plus delta*.
"""
import itertools
from math import gcd

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def find_prime(n, lo):
    """Smallest prime q > lo with n | q-1 and v2(q-1) == v2(n) (faithful, no extra 2-torsion)."""
    vn = v2(n)
    q = ((lo // n) + 1) * n + 1
    while True:
        if q > lo and (q - 1) % n == 0 and v2(q-1) == vn and isprime(q):
            return q
        q += n  # keep n | q-1

def find_gen(p, n):
    # primitive root
    m = p - 1; fac = set(); d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            w = pow(g, (p-1)//n, p)
            return w
    raise RuntimeError

def incidence(a, b, n, mu, k, w, p):
    """# distinct gamma s.t. x^a+gamma x^b in deg<k on some w-subset of mu_n."""
    inv = lambda z: pow(z % p, p-2, p)
    MUa = [pow(x, a, p) for x in mu]
    MUb = [pow(x, b, p) for x in mu]
    s = n - w  # deleted count; we iterate over kept subsets of size w
    gammas = set()
    PAIR = p  # sentinel meaning "whole line agrees" -> direction is degenerate, skip
    for W in itertools.combinations(range(n), w):
        pts = [mu[i] for i in W]
        u0 = [MUa[i] for i in W]
        u1 = [MUb[i] for i in W]
        # order-k divided differences over consecutive (k+1)-windows; each gives a0_J + g a1_J = 0
        def ddk(vals):
            # full table of order-k divided differences across all windows; return list of (a0,a1)?
            pass
        # build per-window divided diff of u0 and u1
        cons = True
        gamma = None
        m = len(pts)
        if m <= k:
            continue  # any gamma works -> infinitely many -> degenerate; skip (w>k required)
        # precompute divided diff of a value vector over a window
        def dd_window(vals, xs):
            vs = list(vals);
            for j in range(1, k+1):
                for i in range(k, j-1, -1):
                    vs[i] = (vs[i] - vs[i-1]) * inv(xs[i] - xs[i-j]) % p
            return vs[k]
        ok = True
        gam = None
        bad = False
        for st in range(m - k):
            xs = pts[st:st+k+1]
            a0 = dd_window(u0[st:st+k+1], xs)
            a1 = dd_window(u1[st:st+k+1], xs)
            if a1 % p == 0:
                if a0 % p != 0:
                    bad = True; break  # 0 = a0 != 0, no gamma
                # else 0=0, this window puts no constraint
                continue
            g = (-a0 * inv(a1)) % p
            if gam is None:
                gam = g
            elif gam != g:
                bad = True; break
        if bad:
            continue
        if gam is None:
            # all windows unconstrained -> any gamma works on this subset -> degenerate direction
            return PAIR
        gammas.add(gam)
    return len(gammas)

def deltastar_and_worst(n, k, p, mu, budget):
    """For each direction find its delta*; report worst (min delta*) directions + the binding-band
       worst direction (max incidence at the global w*)."""
    fars = list(range(k, n))
    dir_ds = {}
    for a, b in itertools.combinations(fars, 2):
        ds = None
        # w from large (shallow) down to k+1; first time I<=budget gives sup delta = 1-w/n at that w
        # incidence increases as w shrinks; find smallest w with I<=budget
        prev = None
        wstar = None
        for w in range(n-1, k, -1):
            I = incidence(a, b, n, mu, k, w, p)
            if I == p:
                continue  # degenerate band for this direction
            if I <= budget:
                wstar = w  # keep going down; we want smallest such w
            else:
                break
        if wstar is not None:
            dir_ds[(a, b)] = 1 - wstar / n
    if not dir_ds:
        return None, None, None
    # worst direction = smallest delta* (binds first)
    min_ds = min(dir_ds.values())
    worst_dirs = [d for d, v in dir_ds.items() if abs(v - min_ds) < 1e-12]
    return min_ds, worst_dirs, dir_ds

def main():
    print("A3 WORST-DIRECTION FAMILY  (faithful big-prime char-0, v2(q-1)=v2(n), q>n^4)\n")
    cases = [(8,2),(16,4),(8,4),(16,8)]
    for n, k in cases:
        rho = k/n
        lo = n**4
        p = find_prime(n, lo)
        mu = [pow(find_gen(p, n), i, p) for i in range(n)]
        budget = n
        min_ds, worst_dirs, dir_ds = deltastar_and_worst(n, k, p, mu, budget)
        if min_ds is None:
            print(f"n={n} k={k} rho={rho}: no non-degenerate direction binds"); continue
        # invariants of worst dirs
        inv_str = []
        for (a,b) in worst_dirs:
            d = gcd(b-a, n)
            inv_str.append(f"(a={a},b={b}: b-a={b-a}, gcd(b-a,n)={d}, a-k={a-k}, b-(n-1)={b-(n-1)}, a/n={a/n:.3f}, b/n={b/n:.3f})")
        print(f"n={n} k={k} rho={rho}: delta*={min_ds:.4f}  worst dir(s):")
        for s in inv_str:
            print("    ", s)
        # also: which dir has the HIGHEST incidence at the global w* (binding band)
        gw = round((1 - min_ds) * n)
        peak = {}
        for (a,b) in dir_ds:
            I = incidence(a,b,n,mu,k,gw,p)
            if I < p:
                peak[(a,b)] = I
        mx = max(peak.values())
        peakdirs = [d for d,v in peak.items() if v==mx]
        print(f"    at binding band w={gw}: max incidence={mx} (budget={budget}); peak dir(s)={peakdirs}")
        print(f"    R4 readout dir would be (n/4={n//4}, 5n/8={5*n//8}); dir(k,k+2)=({k},{k+2})")
        print()

if __name__ == "__main__":
    main()
