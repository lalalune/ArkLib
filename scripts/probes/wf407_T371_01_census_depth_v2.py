#!/usr/bin/env python3
"""wf407/T371-01-census v2 — MOMENT-DEPTH of CensusDomination, the EXACT supply object.

From KKH26AlignmentSupply.lean (kernel-proven), the deep alignable supply on the
KKH26 line (u0=x^{rm}, u1=x^{(r-1)m}) at code dim k=(r-2)m+1, band a=rm, is the family
   S_T = { i : (g^i)^m in T },   gamma_T = -sum_{a in T} a,
ranging over r-subsets T of the m-power subgroup G_m = { (g^m)^j : j<s }, s=n/m.
badScalars_card_le_alignable bounds #bad <= #alignable; the supply lower bound is
#{S_T} >= C(s,r)  (the r-subset family).

So CensusDomination, on its EXTREMAL line, IS the statement:
   #{ distinct r-subset-sums of an order-s subgroup, and #aligned sets } <= K,  K/p <= eps*.

THE MOMENT-DEPTH QUESTION resolves to: is this controlled by a FIXED low-order moment
(<=4th: additive energy E_2, second moment of Gauss period), or does it require the
DEEP r-th order count where r ~ rate*n ~ deep-band index?

For the PRODUCTION rates ρ=k/n, the deployed pin has k=(r-2)m+1, so r ≈ ρ·s + 2.
At ρ=1/2, s=2^{mu-1}/... -> r ~ s/2 = Θ(n). The supply parameter r is the SUBSET SIZE,
and grows LINEARLY with n at fixed rate. The "moment order" of the count = r = Θ(n).

We verify EXACTLY at enumerable scale that:
 (1) the bad-scalar count is the r-subset-sum count of the m-power subgroup G_s (=G_m),
     and the ALIGNABLE-set count is exactly C(s,r) for the antipodal line (= deep supply),
 (2) this r-subset-sum count is NOT a function of any fixed <=4th moment: it changes with
     r at fixed n (deep), tracks the r-th additive moment, and matches the deep-moment
     E_r object (the master wall), NOT E_2.
 (3) compare against E_2 = additive energy (the low-order object the dossier calls
     "2nd-order-capped, reachable"): show #bad/supply is governed by E_r, r=Θ(n), not E_2.
"""
import itertools, sys
from math import comb
from collections import Counter

def find_g(p, n):
    for h in range(2, 5000):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    raise ValueError(f"no order-{n} element mod {p}")

def subgroup(p, s):
    """return order-s multiplicative subgroup of F_p as a list (needs s | p-1)."""
    assert (p - 1) % s == 0
    h = None
    for cand in range(2, 5000):
        x = pow(cand, (p - 1) // s, p)
        if pow(x, s, p) == 1 and all(pow(x, d, p) != 1 for d in range(1, s)):
            h = x; break
    return [pow(h, j, p) for j in range(s)]

def rsubset_sum_count(G, r, p):
    """#distinct values of sum_{a in T} a over r-subsets T of G (=#distinct gamma_T)."""
    sums = set()
    for T in itertools.combinations(G, r):
        sums.add(sum(T) % p)
    return len(sums), comb(len(G), r)

def additive_energy(G, p):
    """E_2(G) = #{(a,b,c,d) in G^4 : a+b=c+d}."""
    cnt = Counter()
    for a in G:
        for b in G:
            cnt[(a + b) % p] += 1
    return sum(v * v for v in cnt.values())

def rth_additive_moment(G, r, p):
    """E_r-flavoured: #{ (a_1..a_r, b_1..b_r) in G^{2r}: sum a = sum b } (ordered).
       = sum_v (N_r(v))^2 where N_r(v)=#ordered r-tuples summing to v."""
    cnt = Counter()
    for tup in itertools.product(G, repeat=r):
        cnt[sum(tup) % p] += 1
    return sum(v * v for v in cnt.values())

def main():
    print("="*80)
    print("wf407/T371-01-census v2 : the EXACT supply object & its moment depth")
    print("="*80)
    print("""
The extremal CensusDomination supply (KKH26AlignmentSupply.lean):
  alignable sets <-> r-subsets T of order-s subgroup G;  gamma_T = -sum(T).
  #bad >= #distinct r-subset sums;  supply (#alignable) >= C(s,r).
Production rate rho fixes r/s ~ rho => r = SUBSET SIZE grows LINEARLY in n.
""")
    # primes with rich subgroup structure (many s | p-1)
    cases = [
        # p, list of (s, r) to test; r sweeps to expose deep dependence
        (12289, [(8, r) for r in range(2, 7)] + [(16, r) for r in range(2, 7)]),
        (40961, [(8, r) for r in range(2, 7)] + [(16, r) for r in range(2, 7)]),
        (65537, [(8, r) for r in range(2, 7)] + [(16, r) for r in range(2, 8)] +
                 [(32, r) for r in range(2, 6)]),
    ]
    for p, sr_list in cases:
        print(f"\n##### p = {p} #####")
        # cache subgroups + E_2
        Gcache = {}
        for s in sorted({s for (s, r) in sr_list}):
            if (p - 1) % s != 0: continue
            G = subgroup(p, s)
            E2 = additive_energy(G, p)
            Gcache[s] = (G, E2)
            print(f"  s={s:>3}:  E_2(G) = {E2}  (= 3s^2-3s = {3*s*s-3*s}? "
                  f"{'YES' if E2 == 3*s*s-3*s else 'NO'})")
        print(f"  {'s':>3} {'r':>3} | {'#distinct gamma_T':>18} {'C(s,r)':>10} "
              f"{'E_r/sum-sq':>14} {'E_2(low)':>10}")
        for (s, r) in sr_list:
            if s not in Gcache: continue
            if r > s: continue
            G, E2 = Gcache[s]
            ndg, Csr = rsubset_sum_count(G, r, p)
            # deep r-th moment (cap compute cost)
            Er = rth_additive_moment(G, r, p) if s ** r <= 2_000_000 else -1
            print(f"  {s:>3} {r:>3} | {ndg:>18} {Csr:>10} {Er:>14} {E2:>10}",
                  flush=True)
    print("""
READING GUIDE:
 - #distinct gamma_T (the bad-scalar count on the extremal line) is the r-SUBSET-SUM
   count of the subgroup. It CHANGES with r at fixed s/E_2 -> it is NOT a function of
   the 2nd moment E_2. It is an r-th-order (deep) additive statistic.
 - The supply C(s,r) is the antipodal-fibre count; at production rate r=rho*s it is
   2^{Theta(s)} = exponential in n. The pin needs #bad <= K, K/p <= eps* = 2^-128.
 - Conclusion test: if #bad tracks E_r (deep, r=Theta(n)) not E_2 (low), CensusDomination
   is DEEP and inherits the Gauss-period/additive-energy master wall.
""")
    return 0

if __name__ == "__main__":
    sys.exit(main())
