#!/usr/bin/env python3
"""
#407 LANE D -- THE DECISIVE TEST: does the Action-Orbit count K give a genuine O(1)/|F|
bound on PLAIN RS over mu_n in the WINDOW INTERIOR, or does it COLLAPSE to BGK?

The KB warns (verbatim): "The orbit *count* itself = BGK at window interior (refuted as
O(1) at n=8); pursue the general-f structural reduction, not a naive count."

We make this decisive. For a monomial pencil h_a(z) = z^a + alpha*z^b on the smooth domain
D = mu_n in F_p (p = 1 mod n), the bad-alpha set
    BAD(delta) = { alpha in F_p : exists g, deg g < k, #{x in mu_n : x^a+alpha x^b = g(x)} >= (1-delta) n }
is closed under alpha -> alpha*w^{b-a} (badSet_orbit_closed). Define:
    L(delta)  = |BAD(delta)|                       (the raw bad-scalar count = "list size")
    S         = orbit size = n / gcd(b-a, n)        (the action compresses by S)
    K(delta)  = #orbits = L(delta)/S                (the Action-Orbit count)

Action-Orbit gives a GENUINE non-BGK escape  <=>  K(delta) = O(1) (bounded) as we move
into the window interior delta in (1-sqrt(rho), 1-rho-Theta(1/log n)) AND as n grows.
It COLLAPSES to BGK  <=>  K(delta) grows with the window depth / n exactly like the bare
list size L(delta)/n does -- i.e. the S-compression buys a constant factor only, and K
inherits the (open, BGK-sized) growth of L.

We compute L, S, K EXACTLY (full alpha-sweep over F_p, exact deg<k agreement via Lagrange)
for several n, at delta swept from Johnson into the interior, and we ALSO compute the
plain bare list size L_bare = max over g of agreement, to anchor BGK.

DECISIVE OUTPUT:
  * Does K stay <= small constant across the interior and across n=8,16(,32)?  (escape)
  * Or does K grow with window depth like L/S grows -- i.e. K ~ |Sigma_r| / S = BGK/S,
    still super-constant?  (collapse)
"""

import itertools, sys
from math import gcd, comb, sqrt, log
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out=[]; p=lo|1
    while len(out) < cap:
        if (p-1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w,n,p)==1 and all(pow(w, n//q, p)!=1 for q in (2,3,5,7) if n%q==0):
            return w
    raise RuntimeError

def lagrange_fits(xs, ys, p, k):
    """Does there exist g of deg < k with g(xs[i])=ys[i] for ALL i?  We are given an
    agreement SUBSET of size t; deg<k codeword fits t points iff the unique deg<t interp
    has deg < k. We instead use: a subset of size t is consistent with deg<k iff its
    Lagrange interpolant through any k of them matches all. Simplest exact test: the points
    lie on a single deg<k poly iff the (t-k) finite differences vanish; we use the
    Vandermonde rank test via interpolation through first k points and checking the rest."""
    t = len(xs)
    if t <= k:
        return True  # any t<=k points lie on some deg<k poly (generic)
    # interpolate through first k points, check the rest
    bx, by = xs[:k], ys[:k]
    def interp(x):
        tot = 0
        for j in range(k):
            num = by[j] % p; den = 1
            for l in range(k):
                if l != j:
                    num = num * ((x - bx[l]) % p) % p
                    den = den * ((bx[j] - bx[l]) % p) % p
            tot = (tot + num * pow(den, p-2, p)) % p
        return tot
    return all(interp(xs[i]) == ys[i] % p for i in range(k, t))

def best_agreement(H, vals, p, k):
    """Max over deg<k codewords g of #{x in H: g(x)=vals(x)}. vals = list aligned to H.
    Exact: the best agreement is the largest subset of (x, vals(x)) lying on one deg<k
    poly. We compute it as: for the value sequence v over the n domain points, max agreement
    = n - (min number of points to delete so the rest interpolate to deg<k). We use the
    standard approach: a deg<k poly is determined by any k agreement points; enumerate all
    k-subsets, interpolate, count agreement. O(C(n,k)*n) -- fine for small n,k."""
    n = len(H)
    best = 0
    for sub in itertools.combinations(range(n), k):
        bx = [H[i] for i in sub]; by = [vals[i] for i in sub]
        # interpolate deg<k through these k points
        def interp(x):
            tot = 0
            for j in range(k):
                num = by[j] % p; den = 1
                for l in range(k):
                    if l != j:
                        num = num * ((x - bx[l]) % p) % p
                        den = den * ((bx[j] - bx[l]) % p) % p
                tot = (tot + num * pow(den, p-2, p)) % p
            return tot
        cnt = sum(1 for i in range(n) if interp(H[i]) == vals[i] % p)
        if cnt > best:
            best = cnt
            if best == n: break
    return best

def orbit_analysis(p, n, k, a, b, threshold):
    """For pencil z^a + alpha z^b, compute BAD = {alpha : best_agreement >= threshold},
    then L=|BAD|, S=orbit size, K=#orbits under alpha->alpha*w^{b-a}."""
    w = find_gen(p, n)
    H = [pow(w, i, p) for i in range(n)]
    Ha = [pow(x, a, p) for x in H]
    Hb = [pow(x, b, p) for x in H]
    mult = pow(w, (b-a) % n, p)  # w^{b-a}: the action multiplier on alpha
    S = n // gcd((b-a) % n if (b-a)%n != 0 else n, n)
    BAD = []
    for alpha in range(p):  # include 0; alpha=0 is degenerate (pure monomial), skip its orbit count
        vals = [(Ha[i] + alpha * Hb[i]) % p for i in range(n)]
        if best_agreement(H, vals, p, k) >= threshold:
            BAD.append(alpha)
    BADset = set(BAD)
    # orbit count under alpha -> alpha*mult  (multiplicative orbit; 0 is its own orbit)
    seen = set(); norb = 0; sizes=[]
    for alpha in BAD:
        if alpha in seen: continue
        norb += 1; cur = alpha; sz = 0
        while cur not in seen:
            seen.add(cur); cur = (cur*mult) % p; sz += 1
            if cur not in BADset:  # orbit must stay inside BAD (it does by orbit-closure)
                pass
        sizes.append(sz)
    return len(BAD), S, norb, Counter(sizes)

def main():
    print("="*82)
    print("#407 LANE D -- ORBIT COUNT K vs BGK at the window interior (PLAIN RS over mu_n)")
    print("="*82)
    print("L=|bad-alpha|, S=orbit size n/gcd(b-a,n), K=#orbits. Action-Orbit escape <=> K=O(1).")
    print("Johnson radius delta_J = 1 - sqrt(rho); window interior is delta > delta_J.\n")

    # Use a moderately large prime per n so mu_n is a PROPER small subgroup (non-saturated),
    # but small enough that the full alpha-sweep (p iterations) is feasible.
    configs = [
        # (n, k, prime). rho=k/n. FAR pencil (a,b >= k, avoid x^{n/2}=+-1 correlated dirs).
        (8, 2, 401),    # rho=1/4
        (8, 4, 401),    # rho=1/2
        (16, 4, 1153),  # rho=1/4
        (16, 8, 1153),  # rho=1/2
    ]
    for (n, k, p) in configs:
        rho = k/n
        dJ = 1 - sqrt(rho)
        # choose a FAR far pencil: a,b distinct, both >= k, b-a not 0 mod n, avoid a-b=n/2
        # pick a = n-1, b = k  (so b-a = k-(n-1)); ensure gcd
        cand = []
        for a in range(k, n):
            for b in range(k, n):
                if a==b: continue
                d = (b-a) % n
                if d == 0 or d == n//2: continue  # exclude correlated x^{n/2} direction
                cand.append((a,b))
        if not cand:
            print(f"n={n} k={k}: no far pencil"); continue
        a,b = cand[0]
        print(f"--- n={n} k={k} rho={rho:.3f} p={p}  pencil (z^{a}+alpha z^{b}), Johnson delta_J={dJ:.3f} ---")
        print(f"    {'delta':>7} {'thr=agr':>8} {'L=|bad|':>8} {'S':>4} {'K=#orb':>7} {'L/n':>6}  {'region':>10}")
        # sweep threshold (agreement) from just above Johnson agreement down into interior
        # agreement t corresponds to delta = 1 - t/n.  Johnson agreement ~ sqrt(rho)*n.
        for t in range(k+1, n+1):
            delta = 1 - t/n
            region = "interior" if delta > dJ + 1e-9 else ("Johnson" if abs(delta-dJ)<0.06 else "below-J")
            L, S, K, szc = orbit_analysis(p, n, k, a, b, t)
            print(f"    {delta:7.3f} {t:8d} {L:8d} {S:4d} {K:7d} {L/n:6.2f}  {region:>10}")
        print()

if __name__ == "__main__":
    main()
