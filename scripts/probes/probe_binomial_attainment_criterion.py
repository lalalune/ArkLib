#!/usr/bin/env python3
"""
probe_binomial_attainment_criterion.py  (#444, #389)

LANE: the EXACT ATTAINMENT CRITERION for the binomial mu_n-incidence dichotomy.

In-tree `binomial_agree_card` (MultiplicativeRigidityZMod) proves the SHARP DICHOTOMY:
    #{x in H : c1 x^a = c2 x^b}  is either 0  OR  exactly gcd(a-b, n),  (n = |H|).
But it does NOT say WHICH branch occurs. The probe c71_trinomial_gcddeg observed the
gcd branch is attained "in the majority"; the binomial fiber over target gamma = c2/c1
is NONEMPTY (=> the gcd branch, card = gcd(d,n)) IFF gamma is a d-th power in H, which
for a cyclic group of order n is equivalent to the clean ORDER criterion

    gamma^(n / gcd(d,n)) = 1                              (d = a - b)

i.e. ord(gamma) | n/gcd(d,n).  This pins the WORST-CASE binomial incidence to EXACTLY
gcd(d,n) (it is realised by any gamma that IS a d-th power, e.g. gamma = 1), turning the
0-or-gcd dichotomy into a usable exact count + worst-case identity.

This probe verifies, over the thin prize-regime mu_n (PROPER subgroup, p == 1 mod n,
(p-1)/n >= 2, large primes incl p > n^3 and Fermat, NEVER n = q-1), the EXACT equivalences:

  (A) #{x in mu_n : x^d = gamma} == ( gcd(d,n) if gamma^(n/gcd) == 1 else 0 )    [criterion]
  (B) the binomial form  #{x in mu_n : c1 x^a = c2 x^b}  == #{x : x^(a-b) == c2/c1} [reduction]
  (C) WORST-CASE over gamma:  max_gamma #{x : x^d == gamma} == gcd(d,n), attained at gamma=1.

Honest scope: a structural exact-count criterion for the binomial strata incidence; it pins
the worst case but is NOT a CORE / Conj-7.1 closure (the strata->soundness bridge stays open).
"""

import sys

def primes_one_mod_n(n, count, min_p=2):
    out = []
    p = max(min_p, n + 1)
    if p % n != 1:
        p += (n - (p % n) + 1) % n
        if p % n != 1:
            p = n * ((p // n) + 1) + 1
    p = n * (max(1, (min_p // n))) + 1
    while p < min_p:
        p += n
    while len(out) < count:
        if p > 1 and is_prime(p) and p % n == 1:
            out.append(p)
        p += n
    return out

def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def subgroup_mu_n(p, n):
    """Return mu_n = unique order-n subgroup of F_p^* (p == 1 mod n)."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    return S, h

def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    factors = factorize(phi)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    raise RuntimeError("no primitive root")

def factorize(m):
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs

def incidence_pow(S, p, d, gamma):
    return sum(1 for x in S if pow(x, d, p) == gamma % p)

def run():
    total = 0
    okA = okB = okC = 0
    failsA = []
    failsB = []
    failsC = []
    # thin: n = 2^a, a in 2..5 ; primes p == 1 mod n with (p-1)/n >= 2, incl p > n^3 and Fermat
    for a in range(2, 6):
        n = 2 ** a
        # gather primes: a spread of p == 1 mod n, plus a Fermat-type if available
        ps = primes_one_mod_n(n, 6, min_p=2 * n + 1)
        # ensure at least one p > n^3
        big = n ** 3 + 1
        ps += primes_one_mod_n(n, 2, min_p=big)
        # Fermat primes 257, 65537 if 1 mod n
        for fp in (257, 65537):
            if fp % n == 1 and fp not in ps:
                ps.append(fp)
        ps = sorted(set(ps))
        for p in ps:
            if (p - 1) // n < 2:   # NEVER n = q-1 (proper subgroup, thinness essential)
                continue
            S, h = subgroup_mu_n(p, n)
            assert len(set(S)) == n, "mu_n must have n distinct elements"
            # exponents a' > b' from degree-<k data; sweep d = a'-b' across 1..n
            for d in range(1, n + 1):
                g = gcd(d, n)
                # sweep gamma over mu_n itself AND a few non-subgroup targets in F_p^*
                gammas = list(S) + [2 % p, (p - 1) % p, 3 % p]
                worst = 0
                for gamma in gammas:
                    cnt = incidence_pow(S, p, d, gamma)
                    # (A) criterion: count == (g if gamma^(n/g)==1 else 0)
                    crit_in = (pow(gamma, n // g, p) == 1)
                    pred = g if crit_in else 0
                    total += 1
                    if cnt == pred:
                        okA += 1
                    else:
                        if len(failsA) < 12:
                            failsA.append((n, p, d, gamma, cnt, pred, g, crit_in))
                    # (B) binomial reduction: pick c1, c2 with c2/c1 == gamma, exponents a'=d+b', b'
                    if gamma != 0 and gamma in S:
                        c1 = 1
                        c2 = gamma
                        b_ = 1
                        a_ = d + b_
                        cntbin = sum(1 for x in S if (c1 * pow(x, a_, p)) % p == (c2 * pow(x, b_, p)) % p)
                        if cntbin == cnt:
                            okB += 1
                        else:
                            if len(failsB) < 12:
                                failsB.append((n, p, d, gamma, cntbin, cnt))
                    if cnt > worst:
                        worst = cnt
                # (C) worst case over gamma == gcd(d,n), attained at gamma=1
                cnt1 = incidence_pow(S, p, d, 1)
                if worst == g and cnt1 == g:
                    okC += 1
                else:
                    if len(failsC) < 12:
                        failsC.append((n, p, d, worst, g, cnt1))
    print(f"(A) criterion  count == (g if gamma^(n/g)==1 else 0):  {okA}/{total} OK")
    print(f"(B) binomial reduction matches x^d fiber:               {okB} OK")
    print(f"(C) worst-case over gamma == gcd(d,n), attained @1:      {okC} OK")
    if failsA:
        print("FAIL (A):", failsA)
    if failsB:
        print("FAIL (B):", failsB)
    if failsC:
        print("FAIL (C):", failsC)
    verdict = (not failsA) and (not failsB) and (not failsC)
    print("VERDICT:", "ALL PASS — attainment criterion CONFIRMED" if verdict else "VIOLATIONS — criterion WRONG")
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(run())
