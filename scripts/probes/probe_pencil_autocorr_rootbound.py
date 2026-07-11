#!/usr/bin/env python3
"""
Probe: the PencilAutocorrelation M=1 root-bound wiring (LEVER K, #407/#444).

CLAIM being formalized (the missing wiring the docstring asserts but never proves):
  If S is a root set inside mu_n and its multiplicative autocorrelation is M(S)=1
  (every nontrivial dilation overlaps S in <= 1 point), then the dilation-pencil
  blocks B_i = zeta_i^{-1} * S (zeta_i in S) are r := |S| blocks of size r, all
  through 1, pairwise meeting ONLY at 1, so by pencil_card_core:
        r*(r-1) + 1 <= n      and hence (r-1)^2 < n  (r <= 1/2 + sqrt(n)).

We verify the COMBINATORIAL chain directly on PROPER thin 2-power subgroups mu_n < F_p*
(p >> n^3, p == 1 mod n, NEVER n = q-1), at synthetic root sets S with autocorr exactly 1,
and confirm:
  (1) M(S)=1  ==>  the r punctured pencil blocks are pairwise disjoint;
  (2) r*(r-1)+1 <= n   holds  (and is TIGHT when S is a perfect-difference / Sidon-like set);
  (3) the COSET-CORE obstruction: when S contains a subgroup H of order d, M(S) >= d,
      so the M=1 hypothesis FAILS (the bound does not apply) -- the honest scope limit.

This is pure finite-group combinatorics (char-free), matching the Lean object exactly.
"""
import random

def mu_n(p, n):
    """Return the order-n subgroup of F_p* (p == 1 mod n), as a sorted list."""
    assert (p - 1) % n == 0
    # find a generator g of F_p*, then h = g^((p-1)/n) has order n
    def order(a):
        o, x = 1, a
        while x != 1:
            x = (x * a) % p
            o += 1
        return o
    g = 2
    while order(g) != p - 1:
        g += 1
    h = pow(g, (p - 1) // n, p)
    H = set()
    x = 1
    for _ in range(n):
        H.add(x)
        x = (x * h) % p
    assert len(H) == n
    return sorted(H), H

def autocorr_max(S, Hset, p):
    """M(S) = max over rho != 1 in F_p* of |S ∩ rho*S|, restricted to rho in mu_n
       (dilations that keep us inside the subgroup -- the pencil shifts are zeta_i*zeta_j^-1 in mu_n)."""
    Sset = set(S)
    best = 0
    best_rho = None
    for rho in Hset:
        if rho == 1:
            continue
        inter = sum(1 for x in S if (rho * x) % p in Sset)
        if inter > best:
            best, best_rho = inter, rho
    return best, best_rho

def punctured_blocks_disjoint(S, p):
    """B_i = zeta_i^{-1} * S for zeta_i in S; punctured C_i = B_i \\ {1}.
       Return True iff all C_i pairwise disjoint."""
    blocks = []
    for z in S:
        zi = pow(z, p - 2, p)  # z^{-1} mod p
        Bi = set((zi * x) % p for x in S)
        Ci = Bi - {1}
        blocks.append(Ci)
    for i in range(len(blocks)):
        for j in range(i + 1, len(blocks)):
            if blocks[i] & blocks[j]:
                return False
    return True

def random_low_autocorr_set(H, Hset, p, r, tries=4000):
    """Try to find an r-subset S of mu_n (containing 1) with multiplicative autocorr exactly 1."""
    Hl = list(H)
    for _ in range(tries):
        S = [1] + random.sample([x for x in Hl if x != 1], r - 1)
        m, _ = autocorr_max(S, Hset, p)
        if m == 1:
            return S
    return None

def main():
    random.seed(7)
    print("=== PROBE: PencilAutocorrelation M=1 root-bound wiring (proper thin mu_n) ===")
    # prize-shaped: p >> n^3, p == 1 mod n, NEVER n = q-1
    configs = [
        (8,  4129),    # 4129 = 8*516+1, prime, >> 8^3=512
        (16, 32801),   # 32801 = 16*2050+1, prime, >> 16^3=4096
        (32, 262337),  # 262337 = 32*8198+1, prime, >> 32^3
    ]
    all_ok = True
    for n, p in configs:
        H, Hset = mu_n(p, n)
        print(f"\n-- n={n}, p={p} (p mod n = {p % n}, p/n^3 = {p/n**3:.1f}, proper subgroup) --")
        # sweep r from small up; find an M=1 set at each r where possible
        max_r_seen = 0
        for r in range(2, n + 1):
            S = random_low_autocorr_set(H, Hset, p, r)
            if S is None:
                continue
            m, _ = autocorr_max(S, Hset, p)
            disj = punctured_blocks_disjoint(S, p)
            bound_ok = (r * (r - 1) + 1 <= n)
            sqrt_ok = ((r - 1) * (r - 1) < n)
            tag = "OK" if (m == 1 and disj and bound_ok and sqrt_ok) else "FAIL"
            if tag == "FAIL":
                all_ok = False
            max_r_seen = max(max_r_seen, r)
            if r <= 4 or r == max_r_seen:
                print(f"   r={r:2d}: M(S)={m}, punctured-disjoint={disj}, "
                      f"r(r-1)+1={r*(r-1)+1}<=n={bound_ok}, (r-1)^2<n={sqrt_ok}  [{tag}]")
        # largest M=1 set found should respect r(r-1)+1 <= n  (i.e. r <= ~1/2+sqrt(n))
        import math
        print(f"   largest M=1 r found = {max_r_seen}, ceiling 1/2+sqrt(n) = {0.5+math.sqrt(n):.2f}")

    # OBSTRUCTION side: a coset-core set has autocorr >= |H_sub|, so M=1 FAILS (honest scope)
    print("\n=== OBSTRUCTION check: coset-core sets violate M=1 (honest scope limit) ===")
    n, p = 16, 32801
    H, Hset = mu_n(p, n)
    Hl = sorted(H)
    # take a subgroup of order d=4 inside mu_16 (the d | n divisor): h^4 has order 4
    # mu_16 has a unique subgroup of each order dividing 16
    def subgroup_of_order(d):
        # element of order d: take generator of mu_n then raise to n/d
        # find generator of H
        def ordsub(a):
            o, x = 1, a
            while x != 1:
                x = (x * a) % p; o += 1
            return o
        gen = next(g for g in Hl if ordsub(g) == n)
        e = pow(gen, n // d, p)
        sub = set()
        x = 1
        for _ in range(d):
            sub.add(x); x = (x * e) % p
        return sub
    for d in (2, 4, 8):
        Hd = subgroup_of_order(d)
        # S = subgroup of order d plus one straggler
        straggler = next(x for x in Hl if x not in Hd)
        S = list(Hd) + [straggler]
        m, rho = autocorr_max(S, Hset, p)
        print(f"   S = mu_{d} ∪ {{straggler}}: |S|={len(S)}, M(S)={m} (>= d={d}? {m>=d}); "
              f"M=1 hypothesis {'HOLDS' if m==1 else 'FAILS (bound inapplicable -> Johnson)'}")

    print("\n=== VERDICT:", "ALL M=1 CONFIGS OK (disjoint + r(r-1)+1<=n + (r-1)^2<n)" if all_ok
          else "FAIL", "===")

if __name__ == "__main__":
    main()
