#!/usr/bin/env python3
"""
#407 LANE D -- the K-GROWTH LAW: settle whether the Action-Orbit count K is O(1) (escape)
or grows like the BGK list size (collapse), via the gap-variety characterization.

KEY SHORTCUT (avoids the O(p) alpha-sweep). For the FAR monomial pencil z^a + alpha z^b at
agreement >= t = (1-delta)n on mu_n, a bad alpha corresponds to a deg<k codeword g and an
agreement set T subset mu_n, |T| >= t, with g - z^a = alpha z^b on T. In the deepest-band /
Kambiré regime the canonical bad family is alpha = e_m(S) for S subset mu_n a "gap config"
(elementary symmetric / power sums vanish in the window), |S| = r*m, where the bad-alpha set
is the DISTINCT-VALUE set { e_m(S) } and its orbit structure under alpha -> alpha*w^{b-a}
is what badSet_orbit_closed counts.

Concretely the proximity-prize bad-scalar count at the window edge is |Sigma_r(mu_s)| =
|H^{(+r)}(mu_s)| = #distinct r-fold sums of mu_s (the Kambire/KB value). The ACTION-ORBIT
count K is that value compressed by the orbit size S = n/gcd(b-a,n) = s (the action is the
dilation by mu_s on the value).

So the decisive question is:  K = |Sigma_r| / S  -- does it stay O(1) as r and n grow into
the window interior, or does it grow (= BGK)?  We compute |Sigma_r(mu_s)| EXACTLY over C
(via Z[zeta] arithmetic) and the orbit count under the natural dilation action, for a range
of (n=s, r), and FIT the growth.

BGK anchor: the bare list size is ~ |Sigma_r| ~ binom(s,r)/(something); the prize needs the
ORBIT count K, not L, to be O(1). We report both and the ratio.
"""

import itertools
from math import gcd, comb, log, sqrt
from collections import Counter

# -- Z[zeta_n] arithmetic, basis {1,zeta,...,zeta^{n/2-1}}, zeta^{n/2} = -1 (n a power of 2)
def add(u,v): return tuple(a+b for a,b in zip(u,v))
def zero(n): return tuple([0]*(n//2))
def root(j,n):
    half=n//2; e=j%n; v=[0]*half
    if e<half: v[e]=1
    else: v[e-half]=-1
    return tuple(v)

def Sigma_r_exact(n, r):
    """Distinct r-fold sums of DISTINCT elements of mu_n, as elements of Z[zeta_n].
    Returns the set of value-vectors (the value spectrum Sigma_r)."""
    half=n//2
    vals=set()
    for comb_idx in itertools.combinations(range(n), r):
        s=zero(n)
        for j in comb_idx: s=add(s, root(j,n))
        vals.add(s)
    return vals

def orbit_count_dilation(vals, n):
    """Orbit count of the value set under the dilation action v -> zeta * v (mult by a
    primitive n-th root), i.e. the Action-Orbit group <mu^{b-a}> acting on the alpha value.
    Multiplying a sum of roots by zeta = shift each exponent by 1: realized on the vector
    by the companion of zeta^(n/2)=-1.  We act by the full mu_n (orbit size up to n)."""
    # multiplication-by-zeta map on Z[zeta_n] in basis {1,...,zeta^{half-1}}, zeta^half=-1:
    half=n//2
    def mul_zeta(v):
        # (sum c_i zeta^i)*zeta = sum c_i zeta^{i+1}; zeta^half = -1
        w=[0]*half
        for i in range(half):
            ni=i+1
            if ni<half: w[ni]+=v[i]
            else: w[0]-=v[i]  # zeta^half = -1
        return tuple(w)
    seen=set(); norb=0; sizes=[]
    valset=set(vals)
    for v in vals:
        if v in seen: continue
        norb+=1; cur=v; sz=0
        while cur not in seen:
            seen.add(cur); cur=mul_zeta(cur); sz+=1
        sizes.append(sz)
    return norb, Counter(sizes)

def main():
    print("="*84)
    print("#407 LANE D -- K-GROWTH LAW: orbit count K vs BGK list size L = |Sigma_r(mu_n)|")
    print("="*84)
    print("Action-Orbit escape <=> K = O(1) as we move into the window interior (r grows, n grows).")
    print("Window interior: r = rho*s + O(1); deeper band = larger r. delta = 1 - r/s + ... .")
    print()
    print(f"{'n':>4} {'r':>3} {'L=|Sigma_r|':>12} {'#orbits K':>10} {'L/n':>8} {'orbit-sizes':>16}")
    # For each n=power of 2, sweep r across the window. The window interior corresponds to
    # r near rho*n for the prize rates; but |Sigma_r| peaks near r=n/2. We sweep r=2..n/2.
    rows=[]
    for n in [8, 16, 32]:
        for r in range(2, n//2 + 1):
            if comb(n, r) > 4_000_000:
                continue
            vals = Sigma_r_exact(n, r)
            L = len(vals)
            K, szc = orbit_count_dilation(vals, n)
            szrepr = dict(szc)
            print(f"{n:>4} {r:>3} {L:>12} {K:>10} {L/n:>8.2f} {str(szrepr):>16}")
            rows.append((n,r,L,K))
        print()

    print("="*84)
    print("VERDICT TEST: as n doubles (8->16->32) at FIXED window depth (r = rho*n, rho=1/4),")
    print("does K stay O(1) [escape] or grow [collapse]?  rho=1/4 => r = n/4.")
    print(f"{'n':>4} {'r=n/4':>6} {'L=|Sigma_r|':>12} {'K=#orbits':>10}  {'K growth':>10}")
    prevK=None
    for n in [8,16,32,64]:
        r=n//4
        if comb(n,r) > 4_000_000:
            print(f"{n:>4} {r:>6} {'(too big)':>12}")
            continue
        vals=Sigma_r_exact(n,r); L=len(vals); K,_=orbit_count_dilation(vals,n)
        g = "" if prevK is None else f"x{K/prevK:.2f}"
        print(f"{n:>4} {r:>6} {L:>12} {K:>10}  {g:>10}")
        prevK=K

    print()
    print("="*84)
    print("Same at rho=1/2 (r=n/2, the densest, |Sigma_r| largest):")
    print(f"{'n':>4} {'r=n/2':>6} {'L=|Sigma_r|':>12} {'K=#orbits':>10}  {'K growth':>10}")
    prevK=None
    for n in [8,16,32]:
        r=n//2
        if comb(n,r) > 5_000_000:
            print(f"{n:>4} {r:>6} {'(too big)':>12}"); continue
        vals=Sigma_r_exact(n,r); L=len(vals); K,_=orbit_count_dilation(vals,n)
        g = "" if prevK is None else f"x{K/prevK:.2f}"
        print(f"{n:>4} {r:>6} {L:>12} {K:>10}  {g:>10}")
        prevK=K

if __name__ == "__main__":
    main()
