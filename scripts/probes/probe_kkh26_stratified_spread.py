#!/usr/bin/env python3
"""Falsify-first probe for issue #334 hypothesis A2: KKH26 (ePrint 2026/782) Lemma 1
stratified by antipodal pairs.

Setting: G = multiplicative subgroup of F_p of size s (s a power of 2), p == 1 (mod s),
p > s^{s/2}.  Since s is even, -1 = g^{s/2} is in G, so G is a disjoint union of s/2
antipodal pairs {x, -x}.

KKH26 Lemma 1 counts only "sign-free" subsets S (S cap (-S) empty): there are exactly
2^r * C(s/2, r) of them, and the lemma claims their sums are pairwise distinct, giving
that many distinct r-element sums.

Hypothesis A2 (stratification): every r-subset S decomposes as (j antipodal pairs)
disjoint-union (sign-free S' of size r-2j); the pairs sum to 0, so
   {sums of all r-subsets} = union over feasible j of V_{r-2j},
where V_t = {distinct sums of sign-free t-subsets} (V_0 = {0}), and stratum j is
feasible iff 0 <= 2j <= r and (r-2j) + j <= s/2 (need j pairs disjoint from the t
pairs the sign-free part touches).  A2 claims the union is strictly larger than the
paper's sign-free count |V_r| alone, with strata (conjecturally) pairwise disjoint.

This probe, with EXACT integer arithmetic:
  s = 8 : smallest prime p == 1 (mod 8),  p > 8^4  = 4096;        r in 2..6
  s = 16: smallest prime p == 1 (mod 16), p > 16^8 = 4294967296;  r in 2..8
For each (s, r) it enumerates ALL C(s, r) subsets, computes the exact distinct-sum
count, the sign-free-only count, the paper bound 2^r*C(s/2,r), each stratum V_t and
all pairwise stratum intersections, and checks whether 0 (the j = r/2 stratum value)
is already a sign-free r-sum.

Asserts (exit 0 iff all pass):
  * tautology: union of feasible strata == all-subsets distinct sums (set equality);
  * paper bound: |V_r| == 2^r*C(s/2,r) when r <= s/2 (Lemma 1 sums all distinct),
    hence in particular >= the paper's lower bound;
  * monotone sanity: all-subsets count >= sign-free count; |V_t| matches its
    subset count or is at least 1 when t = 0.
"""

from itertools import combinations
from math import comb
import sys

# ---------------------------------------------------------------- primality (exact)

def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin, valid far beyond 2^64 with these bases."""
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def smallest_prime_1_mod(s: int, lower: int) -> int:
    """Smallest prime p with p > lower and p == 1 (mod s)."""
    p = lower - (lower % s) + 1  # == 1 mod s
    while p <= lower or not is_prime(p):
        p += s
    return p

# ---------------------------------------------------------------- subgroup of order s

def order_s_subgroup(p: int, s: int) -> list[int]:
    """The (unique) multiplicative subgroup of F_p^x of order s (s | p-1, s = 2^k).
    Found via h = a^((p-1)/s) with h^(s/2) != 1 (suffices for s a power of 2)."""
    assert (p - 1) % s == 0
    e = (p - 1) // s
    for a in range(2, 10_000):
        h = pow(a, e, p)
        if pow(h, s // 2, p) != 1:
            G = sorted(pow(h, i, p) for i in range(s))
            assert len(set(G)) == s, "h does not have order s"
            # closure under negation: -1 = h^(s/2) in G
            assert all((p - x) % p in set(G) for x in G), "G not closed under x -> -x"
            return G
    raise RuntimeError("no generator found")

# ---------------------------------------------------------------- per-(s,r) analysis

def analyze(s: int, p: int, r_range: range) -> list[dict]:
    G = order_s_subgroup(p, s)
    Gset = set(G)
    half = s // 2
    # antipodal pair representatives (one element per pair {x, -x})
    reps = []
    seen: set[int] = set()
    for x in G:
        if x not in seen:
            reps.append(x)
            seen.add(x)
            seen.add((p - x) % p)
    assert len(reps) == half

    def sign_free_sums(t: int) -> set[int]:
        """V_t: distinct sums of sign-free t-subsets (exact, mod p)."""
        if t == 0:
            return {0}
        if t > half:
            return set()
        out: set[int] = set()
        for pair_choice in combinations(reps, t):
            for signs in range(1 << t):
                acc = 0
                for k, x in enumerate(pair_choice):
                    acc += x if (signs >> k) & 1 == 0 else p - x
                out.add(acc % p)
        return out

    rows = []
    max_t = max(r_range)
    V = {t: sign_free_sums(t) for t in range(0, max_t + 1)}

    for r in r_range:
        # (a) all r-subsets, exact distinct sums
        all_sums: set[int] = set()
        n_all = 0
        for S in combinations(G, r):
            all_sums.add(sum(S) % p)
            n_all += 1
        assert n_all == comb(s, r)

        # (b) sign-free only
        n_sf = (2 ** r) * comb(half, r)  # exact count of sign-free r-subsets
        sf_sums = V[r] if r <= half else set()
        paper_bound = n_sf  # paper's claimed lower bound on distinct sign-free sums

        # (c) stratified prediction: union over feasible j of V_{r-2j}
        feasible_j = [j for j in range(0, r // 2 + 1) if (r - 2 * j) + j <= half]
        strata = {j: V[r - 2 * j] for j in feasible_j}
        union: set[int] = set()
        for vs in strata.values():
            union |= vs

        # pairwise intersections of strata
        inters = {}
        js = sorted(strata)
        for i1 in range(len(js)):
            for i2 in range(i1 + 1, len(js)):
                a, b = js[i1], js[i2]
                inters[(a, b)] = len(strata[a] & strata[b])
        disjoint = all(v == 0 for v in inters.values())

        zero_in_Vr = 0 in sf_sums

        rows.append(dict(
            s=s, p=p, r=r,
            paper_bound=paper_bound,
            sign_free_exact=len(sf_sums),
            all_subsets_exact=len(all_sums),
            stratified_union=len(union),
            feasible_j=feasible_j,
            strata_sizes={j: len(strata[j]) for j in feasible_j},
            pairwise_intersections=inters,
            strata_pairwise_disjoint=disjoint,
            zero_is_signfree_r_sum=zero_in_Vr,
            union_equals_all=(union == all_sums),
        ))
    return rows

# ---------------------------------------------------------------- main

def main() -> int:
    configs = [
        (8, smallest_prime_1_mod(8, 8 ** 4), range(2, 7)),       # p > 4096
        (16, smallest_prime_1_mod(16, 16 ** 8), range(2, 9)),    # p > 4294967296
    ]
    failures = []
    print(f"{'s':>3} {'r':>2} {'paper':>8} {'signfree':>9} {'all':>9} "
          f"{'union':>9} {'disj':>5} {'0inVr':>5}  strata sizes / intersections")
    for s, p, rr in configs:
        print(f"-- s={s}: p = {p} (p == 1 mod {s}, p > {s}^{s//2} = {s**(s//2)}), "
              f"prime: {is_prime(p)}")
        for row in analyze(s, p, rr):
            print(f"{row['s']:>3} {row['r']:>2} {row['paper_bound']:>8} "
                  f"{row['sign_free_exact']:>9} {row['all_subsets_exact']:>9} "
                  f"{row['stratified_union']:>9} "
                  f"{str(row['strata_pairwise_disjoint']):>5} "
                  f"{str(row['zero_is_signfree_r_sum']):>5}  "
                  f"j->|V|: {row['strata_sizes']}  "
                  f"cap: {row['pairwise_intersections']}")
            # --- assertions -------------------------------------------------
            # tautology check: stratified union must equal all-subsets sums
            if not row['union_equals_all']:
                failures.append((s, row['r'], "stratified union != all-subset sums"))
            # paper bound: distinct sign-free sums >= 2^r * C(s/2, r)
            if row['sign_free_exact'] < row['paper_bound']:
                failures.append((s, row['r'], "paper lower bound FAILS"))
            # Lemma 1 tightness: sums of distinct sign-free subsets all distinct
            if row['sign_free_exact'] != row['paper_bound']:
                failures.append((s, row['r'],
                                 "sign-free sums not all distinct (Lemma 1 not tight)"))
            # monotone sanity
            if row['all_subsets_exact'] < row['sign_free_exact']:
                failures.append((s, row['r'], "all-subsets < sign-free (impossible)"))
            if row['stratified_union'] < max(row['strata_sizes'].values()):
                failures.append((s, row['r'], "union smaller than a stratum"))
        print()

    # verdict
    gains = []
    for s, p, rr in configs:
        for row in analyze(s, p, rr):
            sf, al = row['sign_free_exact'], row['all_subsets_exact']
            if sf > 0:
                gains.append((s, row['r'], al - sf, 100.0 * (al - sf) / sf))
            else:
                gains.append((s, row['r'], al, float('inf')))
    strict = [g for g in gains if g[2] > 0]
    print("strict gains (s, r, all-signfree, %):")
    for g in gains:
        print(f"  s={g[0]} r={g[1]}: +{g[2]} ({g[3]:.4f}%)")

    if failures:
        print("FAILURES:", failures)
        return 1
    print("ALL ASSERTIONS PASS")
    print(f"verdict: stratification strictly increases the distinct-sum count in "
          f"{len(strict)}/{len(gains)} (s,r) cells")
    return 0


if __name__ == "__main__":
    sys.exit(main())
