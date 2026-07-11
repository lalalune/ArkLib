#!/usr/bin/env python3
"""#389: zero-sum-triple count / additive energy of 2-power NTT domains μ_{2^k}
over F_p (n = 2^k | p−1).  The cubic orchard identity (in-tree) makes this the
EXACT m=0 cubic supply; the smooth cubic bound reduces it to E(μ_n).

Char-0 Mann rigidity says three 2-power roots of unity never sum to 0 (no cube
roots in μ_{2^k}).  Over F_p that theorem does NOT apply — this probe measures
what actually survives, looking for:
  (a) ZeroSumTriples Z(n) = #{(a,b,c) ∈ μ_n³ : a+b+c = 0} exactly;
  (b) the additive energy E(n) = Σ_t r(t)²;
  (c) max_{t≠0} r(t)  vs the GV ceiling 4 n^{2/3};
  (d) whether Z(n)/n or E(n)/n² stay bounded / grow, across many p for fixed n.
"""

import sys


def find_generator_order(p, n):
    """A generator of the order-n subgroup of F_p^*, given n | p-1."""
    assert (p - 1) % n == 0
    g = None
    e = (p - 1) // n
    for a in range(2, p):
        cand = pow(a, e, p)
        if cand != 1:
            # order of cand divides n; ensure it's exactly n
            ok = all(pow(cand, n // q, p) != 1 for q in prime_factors(n))
            if ok:
                g = cand
                break
    return g


def prime_factors(n):
    fs = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return fs


def subgroup(p, n):
    g = find_generator_order(p, n)
    assert g is not None
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = x * g % p
    assert len(set(G)) == n
    return G


def stats(p, n):
    G = subgroup(p, n)
    Gset = set(G)
    # rep counts r(t) = #{(a,b) in G^2 : a+b = t}
    from collections import defaultdict
    r = defaultdict(int)
    for a in G:
        for b in G:
            r[(a + b) % p] += 1
    E = sum(v * v for v in r.values())
    Z = sum(r[(-c) % p] for c in G)  # zero-sum triples
    maxr = max((v for t, v in r.items() if t != 0), default=0)
    return Z, E, maxr, r[0]


def main():
    # primes p ≡ 1 mod n for several 2-power n
    targets = {
        8:  [17, 41, 73, 89, 97, 113, 137, 193, 233, 241, 257, 281, 313, 337, 353, 401, 409, 433, 449, 457, 521, 569, 577, 593, 601, 617, 641, 673, 761, 769],
        16: [17, 97, 113, 193, 241, 257, 337, 353, 433, 449, 577, 593, 641, 673, 769, 881, 929, 977, 1009, 1153, 1201, 1217, 1249, 1297],
        32: [97, 193, 257, 353, 449, 577, 641, 673, 769, 929, 1153, 1217, 1249, 1297, 1409, 1601, 1697, 1761 if False else 1889, 2017, 2081],
        64: [193, 257, 449, 577, 641, 769, 1153, 1217, 1601, 1697, 2113, 2273, 2369, 2689, 2753, 3137, 3329, 3457, 3617, 3673 if False else 3833],
    }
    print("=== zero-sum triples / additive energy of μ_{2^k} ⊂ F_p ===")
    print(f"{'n':>4} {'#p':>4} {'Zmin':>6} {'Zmax':>6} {'Zmean':>7} {'n^(5/3)':>8} "
          f"{'maxr_max':>8} {'4n^2/3':>7} {'E/n^2 max':>9} {'r0':>4}")
    for n in sorted(targets):
        ps = [p for p in targets[n] if (p - 1) % n == 0]
        Zs, Es, maxrs, r0s = [], [], [], []
        for p in ps:
            Z, E, maxr, r0 = stats(p, n)
            Zs.append(Z); Es.append(E); maxrs.append(maxr); r0s.append(r0)
        n53 = n ** (5 / 3)
        gv = 4 * n ** (2 / 3)
        En2max = max(Es) / n ** 2
        print(f"{n:>4} {len(ps):>4} {min(Zs):>6} {max(Zs):>6} {sum(Zs)/len(Zs):>7.1f} "
              f"{n53:>8.1f} {max(maxrs):>8} {gv:>7.1f} {En2max:>9.3f} {r0s[0]:>4}")
    print()
    # Does max_t r(t) ever exceed the GV ceiling? (GVRepBound certification surrogate)
    print("=== GV ceiling check: any t≠0 with r(t) > 4 n^{2/3}? ===")
    viol = 0
    total = 0
    for n in sorted(targets):
        for p in targets[n]:
            if (p - 1) % n != 0:
                continue
            _, _, maxr, _ = stats(p, n)
            total += 1
            if maxr > 4 * n ** (2 / 3):
                viol += 1
                print(f"  n={n} p={p}: max r(t) = {maxr} > {4*n**(2/3):.1f}")
    print(f"GV ceiling violations: {viol}/{total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
