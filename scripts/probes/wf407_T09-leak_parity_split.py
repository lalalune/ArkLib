#!/usr/bin/env python3
"""
wf407_T09-leak_parity_split.py  --  #407 thread T09-leak.  CORRECTED leak definition.

From RESEARCH_SYNTHESIS_407_CONNECTIONS.md C042 (RESULTS sec 17):
    #cross-parity-defects = |S0 cap (-g) S0|,
    S0 = (mu_{n/2}-subset-sum image) subset F_q,  g = generator of mu_n / mu_{n/2} (~ Z/2).

THE CROSS-PARITY LEAK.  mu_n splits as mu_{n/2} sqcup g*mu_{n/2} (even / odd powers; g = h, the
generator, with h^{n/2} = -1 since -1 in mu_n is the unique order-2 element).  A *cross-parity*
defect is a coincidence
       A == B   (mod p),     A in S0 = subset-sums over mu_{n/2}  (EVEN powers),
                             B in g * S0 = subset-sums over the ODD-power coset.
Writing B = g * B' with B' in S0, the relation is  A == g*B', i.e. A == -g0 * B'  with the
parity unit g (the claim "A == -g B mod q").  The defect count is then the self-intersection
|S0 cap g*S0| of the SAME image S0 under the multiplicative dilate g.

We MEASURE, at n=16,32,64 and several prize-shaped primes p ~ n^beta:
 (L1) Among ALL depth-r defects (spurious mod-p balanced relations), what fraction is
      "cross-parity": expressible with one side wholly in mu_{n/2}, the other wholly in g*mu_{n/2}?
 (L2) Independently, measure |S0 cap g*S0| / |S0| directly (the dilate self-intersection) -- this
      IS the cross-parity defect count per C042; compare its growth to the BGK additive-energy
      excess and to |S0|/q (Conj 1.12 spreading).
 (L3) Test (3) of the target: is the dilate self-intersection bounded by anything BELOW the
      full additive-energy / sum-product BGK quantity?  i.e. does the parity/dilate structure
      give a count strictly better than E_2(mu_{n/2})?
"""
import math, itertools, sys
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    return None

def smallest_prime_1_mod(n, lo):
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def subgroup_gen(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return h, g

def S0_image(p, h2, half):
    """S0 = set of ALL subset-sums (any subset, including empty -> 0) of mu_{n/2} = <h2>.
    Built incrementally: reachable = reachable union (reachable + element).  O(half * |S0|),
    EXACT over all 2^half subsets regardless of half."""
    mu_half = [pow(h2, i, p) for i in range(half)]
    reach = {0}
    for x in mu_half:
        reach |= set((s + x) % p for s in reach)
    return reach, mu_half

def E2_subgroup(p, mu):
    """additive energy E_2 of the SET mu: #{(a,b,c,d): a+b == c+d}."""
    from collections import Counter
    sums = Counter()
    for a in mu:
        for b in mu:
            sums[(a+b) % p] += 1
    return sum(c*c for c in sums.values())

def main():
    print("="*112)
    print("T09-leak  parity-split definition: S0 = mu_{n/2}-subset-sum image; defect = |S0 cap g*S0|")
    print("="*112)
    for n in (16, 32, 64):
        half = n // 2
        print(f"\n############  n={n}  (mu_{{n/2}} order {half})  ############")
        for beta in (4.0, 4.5, 5.0):
            base = int(n**beta)
            p = smallest_prime_1_mod(2*n, base)   # need mu_{2n} too for clean g handling
            h, g0 = subgroup_gen(p, n)
            # parity generator g = h (mu_n = <h>); mu_{n/2} = <h^2>; coset gen = h; -1 = h^{n/2}
            h2 = pow(h, 2, p)
            minus1 = pow(h, half, p)
            assert minus1 == p-1, f"expected h^(n/2) = -1, got {minus1} (p-1={p-1})"
            img, mu_half = S0_image(p, h2, half)
            S0 = img
            # dilate by g = h: cross-parity defect count = |S0 cap h*S0|
            hS0 = set((h*x) % p for x in S0)
            inter = S0 & hS0
            # also dilate by -h (the literal -g):
            mhS0 = set(((p-h)*x) % p for x in S0)
            inter_m = S0 & mhS0
            # baselines
            sizeS0 = len(S0)
            density = sizeS0 / p
            E2half = E2_subgroup(p, mu_half)
            # number of subset-sum REPRESENTATIONS colliding under dilate (with multiplicity) would be
            # the true defect count; here we report set-incidence as in C042.
            print(f"  beta={beta} p={p} (2^{math.log2(p):.1f}): |S0|={sizeS0} (dens {density:.3f})  "
                  f"|S0 cap hS0|={len(inter)} ({len(inter)/sizeS0:.3f}|S0|, {len(inter)/p:.4f}q)  "
                  f"|S0 cap -hS0|={len(inter_m)}  E2(mu_{half})={E2half} ({E2half/half**2:.2f}*half^2)")
    print("\n" + "="*112)
    print("READINGS:")
    print("  - |S0 cap g*S0|/|S0| = the self-intersection fraction under the parity dilate g.")
    print("    If this is ~1 (S0 nearly dilate-invariant) the defect count ~ |S0| (huge).")
    print("    If S0 is large (Conj 1.12 spreading, density->1) the intersection is automatically")
    print("    ~ |S0|^2/p (random overlap) -> a sum-product / BGK-energy quantity, NOT smaller.")
    print("  - The leak gives a COUNT only as good as you can bound |S0 cap g*S0|; that bound is the")
    print("    additive-energy / Stepanov wall E_2(mu_{n/2}) (sum-product). No structural shortcut.")

if __name__ == "__main__":
    main()
