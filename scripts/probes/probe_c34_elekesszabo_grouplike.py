#!/usr/bin/env python3
"""
C34 ATTACK -- Elekes-Szabo Group-Like Expansion for the Far-Line Incidence.

CONJECTURE C34 claims: framing the far-line incidence as an Elekes-Szabo (ES)
group-like configuration, the ES structure theorem forces EITHER a constant list
(past-Johnson pin) OR a special algebraic relation EXCLUDED by the dyadic
structure at prize scale.

The decisive question for ES: is the bad-(scalar, codeword-set) incidence relation
  - CARTESIAN/general-position  => ES gives a subquadratic O(n^{2-eta}) bound (would pin), OR
  - GROUP-LIKE (graph of a group action) => ES lands on its EXCEPTIONAL branch and
    gives NO nontrivial bound (consistent with large counts; cannot cap them).

ES dichotomy (Elekes-Szabo 2012, Raz-Sharir-de Zeeuw): an algebraic surface
F(x,y,z)=0 either has incidences << N^{2-eta}, OR is "group-like": locally
F(x,y,z)=0 <=> phi(x)+psi(y)+chi(z)=0 for a 1-dim group, i.e. the graph of a
group operation. The group-like branch is EXACTLY where no subquadratic bound holds.

This probe TESTS, reproducibly over proper subgroups mu_n (p PRIME, p >> n^3, NEVER
n=p-1), whether the far-line bad-scalar relation is dilation-equivariant:

    gamma_T  =  - h_{a-k}(T) / h_{b-k}(T)            (unique bad scalar for (k+1)-subset T)
    gamma_{w^s . T}  =?=  w^{s(a-b)} . gamma_T        (group-like / dilation-equivariant)

where h_m = complete homogeneous symmetric poly (top divided difference of x^m on a
(k+1)-set), and w = primitive n-th root in F_p. If equivariance holds EXACTLY, the
relation is the graph of the mu_n action z -> w^{a-b} z  =>  ES exceptional branch
=> ES gives NO incidence bound => C34's "Cartesian" horn never fires.

We also test the SECOND horn of C34: does the DYADIC structure EXCLUDE the group-like
relation? Answer must be measured: if the dyadic mu_n itself IS the acting group, the
dyadic structure TRIGGERS (does not exclude) the exceptional branch.
"""

import itertools, sys
from math import gcd
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
    out = []
    p = ((lo // n) + 1) * n + 1
    while len(out) < cap:
        if is_prime(p):
            out.append(p)
        p += n
    return out

def find_gen(p, n):
    """primitive n-th root of unity in F_p (p = 1 mod n)."""
    g = 2
    while True:
        w = pow(g, (p - 1) // n, p)
        # check order exactly n
        ok = pow(w, n, p) == 1
        if ok:
            order_full = True
            d = 1
            for q in set(prime_factors(n)):
                if pow(w, n // q, p) == 1:
                    order_full = False
                    break
            if order_full:
                return w
        g += 1

def prime_factors(n):
    f = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d); n //= d
        d += 1
    if n > 1: f.append(n)
    return f

def h_complete(m, T, p):
    """complete homogeneous symmetric poly h_m of the multiset T (mod p).
    h_m = sum over multisets of size m of products. Use generating function
    coefficient: prod 1/(1 - t_i x) -> coeff of x^m. Compute via recurrence
    using power sums (Newton) OR directly via DP over elements."""
    # DP: dp[j] = h_j of processed elements. Adding element t:
    # new h_j = sum_{i<=j} t^{j-i} * old h_i  (i.e. h_j(S+{t}) = h_j(S)+t*h_{j-1}(S+{t}))
    dp = [0] * (m + 1)
    dp[0] = 1
    for t in T:
        for j in range(1, m + 1):
            dp[j] = (dp[j] + t * dp[j - 1]) % p
    return dp[m]

def test_equivariance(n, k, a, b, p, w, num_subsets=400, seed=12345):
    """For random (k+1)-subsets T of mu_n, check
         gamma_{w^s . T} == w^{s(a-b)} * gamma_T   for all shifts s.
    gamma_T = - h_{a-k}(T) / h_{b-k}(T)  (mod p), when h_{b-k}(T) != 0."""
    mu = [pow(w, i, p) for i in range(n)]
    import random
    rng = random.Random(seed)
    checks = 0
    fails = 0
    skipped = 0
    am = a - k  # h index for top divided diff of x^a on (k+1)-set
    bm = b - k
    if am < 0 or bm < 0:
        return None
    seen = set()
    tries = 0
    while checks < num_subsets and tries < num_subsets * 20:
        tries += 1
        idx = tuple(sorted(rng.sample(range(n), k + 1)))
        if idx in seen:
            continue
        seen.add(idx)
        T = [mu[i] for i in idx]
        hb = h_complete(bm, T, p)
        if hb == 0:
            skipped += 1
            continue
        ha = h_complete(am, T, p)
        gamma = (-ha * pow(hb, p - 2, p)) % p
        # test all dilation shifts s = 1..n-1
        ok_all = True
        for s in range(1, n):
            ws = pow(w, s, p)
            Ts = [(ws * t) % p for t in T]
            hbs = h_complete(bm, Ts, p)
            has = h_complete(am, Ts, p)
            if hbs == 0:
                # equivariance must also send 0 -> 0
                continue
            gamma_s = (-has * pow(hbs, p - 2, p)) % p
            pred = (pow(w, (s * (a - b)) % (p - 1), p) * gamma) % p
            if gamma_s != pred:
                ok_all = False
                break
        checks += 1
        if not ok_all:
            fails += 1
    return dict(checks=checks, fails=fails, skipped=skipped)

def bad_scalar_set_and_orbits(n, k, a, b, p, w):
    """Compute the full set of bad scalars at the FIRST band (w_band = k+1):
    for each (k+1)-subset T, gamma_T (if h_{b-k}(T) != 0). Collect distinct
    gammas. Then verify the set is closed under gamma -> w^{a-b} gamma
    (orbit closure = group-like), and report orbit structure under mu_d,
    d = n / gcd(a-b, n)."""
    mu = [pow(w, i, p) for i in range(n)]
    am, bm = a - k, b - k
    gammas = set()
    for idx in itertools.combinations(range(n), k + 1):
        T = [mu[i] for i in idx]
        hb = h_complete(bm, T, p)
        if hb == 0:
            continue
        ha = h_complete(am, T, p)
        gamma = (-ha * pow(hb, p - 2, p)) % p
        gammas.add(gamma)
    # action multiplier
    mult = pow(w, (a - b) % (p - 1), p)
    # closure check
    closed = all(((mult * g) % p) in gammas for g in gammas)
    # orbit structure under <mult> (cyclic subgroup of F_p^*)
    # order of mult = n / gcd(a-b, n)
    d = n // gcd((a - b) % n if (a - b) % n != 0 else n, n)
    orbits = []
    rem = set(gammas)
    while rem:
        g0 = rem.pop()
        orb = {g0}
        g = (mult * g0) % p
        while g != g0:
            orb.add(g)
            rem.discard(g)
            g = (mult * g) % p
        orbits.append(len(orb))
    return dict(num_bad=len(gammas), closed=closed, action_order=d,
                num_orbits=len(orbits), orbit_sizes=sorted(Counter(orbits).items()))

def main():
    print("=" * 78)
    print("C34: Elekes-Szabo group-like test for far-line incidence over mu_n")
    print("Honesty: proper subgroup mu_n, p PRIME, p >> n^3, NEVER n=p-1")
    print("=" * 78)
    # prize-shaped tiny instances: dyadic n = 2^mu, k = rho*n, far direction (a,b)
    configs = [
        # (n, k, a, b)  -- a,b are the far monomial exponents of pencil x^a + g x^b
        (8,  2, 5, 3),
        (8,  1, 6, 2),
        (16, 4, 9, 5),
        (16, 2, 11, 3),
        (16, 4, 13, 7),
        (32, 4, 17, 9),
        (32, 8, 21, 11),
    ]
    for (n, k, a, b) in configs:
        # p prime, p = 1 mod n, p >> n^3 (so dyadic mu_n is a PROPER subgroup, n != p-1)
        lo = max(50 * n * n * n, n * n * n + 10)
        ps = primes_1_mod_n(n, lo, 3)
        print(f"\n--- n={n} (mu={n.bit_length()-1} dyadic), k={k} (rho={k/n}), "
              f"far pencil x^{a}+g*x^{b}, a-b={a-b} ---")
        for p in ps:
            assert is_prime(p) and (p - 1) % n == 0 and p > n * n * n
            assert n != p - 1, "VIOLATION: n=p-1 forbidden"
            w = find_gen(p, n)
            eq = test_equivariance(n, k, a, b, p, w, num_subsets=300)
            orb = bad_scalar_set_and_orbits(n, k, a, b, p, w) if n <= 16 else None
            tag = (f"p={p} (p/n^3={p/(n**3):.1f}x): "
                   f"equivariance checks={eq['checks']} FAILS={eq['fails']} "
                   f"skip={eq['skipped']}")
            print("  " + tag)
            if orb is not None:
                print(f"      band-1 bad-scalars={orb['num_bad']}  "
                      f"closed_under_action={orb['closed']}  "
                      f"action_order(mu_d)={orb['action_order']}  "
                      f"#orbits={orb['num_orbits']}  orbit_sizes={orb['orbit_sizes']}")
    print("\n" + "=" * 78)
    print("VERDICT LOGIC:")
    print(" - FAILS=0 everywhere => relation is dilation-equivariant = GROUP-LIKE")
    print("   => ES lands on its EXCEPTIONAL branch => ES gives NO incidence bound.")
    print(" - closed_under_action=True, orbits are full mu_d-cosets => the dyadic mu_n")
    print("   IS the acting group => dyadic structure TRIGGERS (not excludes) the")
    print("   exceptional branch => C34's 'special relation excluded by dyadic' is")
    print("   backwards; the dyadic structure is precisely WHAT MAKES it group-like.")
    print("=" * 78)

if __name__ == "__main__":
    main()
