#!/usr/bin/env python3
"""Independent adversarial verification of the delta* KEYSTONE: E_{F_p}(mu_n) (#389).

The delta* floor now reduces (lalalune/moon, 2026-06-13) to ONE statement:
E_{F_p}(mu_n) <= C*n^2 for the split 2-power subgroup, claimed = 3n(n-1) exactly with
transfer threshold "sharp at ~n^2.3". This is a FROM-SCRATCH cross-check (different code
path than the swarm's probe_split_energy.py): E = sum_s (#{(a,b) in mu_n^2 : a+b=s})^2.

FINDINGS (n = 8..128, multiple primes p == 1 mod n):
 1. CORROBORATED: E = 3n(n-1) EXACTLY at generic/large p, every n. The keystone value
    the pin rests on is independently confirmed.
 2. CORRECTION to "sharp at n^2.3": the sub-threshold surplus is PRIME-SPECIFIC and
    NON-MONOTONE in p, not a clean power-of-n cutoff. E.g. n=32 is CLEAN at p=3041
    (~n^2.3) and p=2081/1601 but has SURPLUS at p=4129 (~n^2.4, ABOVE the nominal
    threshold). So "E=3n(n-1) for p >= n^c" is FALSE for any fixed c near 2.3; the
    correct hypothesis is a cyclotomic-norm/divisibility condition on p, not a power.
 3. mechanism: NOT a literal small integer in mu_n (diagnostic: none of 2,3,5,6,7 in
    mu_n at the surplus primes) -- it is a subtler norm-divisibility (two-layer) event.
 4. CAVEAT (honest): in this sample E/n^2 stayed in [2.8, 3.9], but this is SAMPLED,
    not a proof; the HBK worst case is E << n^2.5 > n^2, so E <= C*n^2 is NOT
    unconditional and the transfer threshold is genuinely needed -- this probe does
    not claim otherwise.
Exact integer arithmetic; deterministic Miller-Rabin primality.
"""
from collections import Counter

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(w, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True

def prime_1_mod_n_ge(x, n):
    p = x + ((1 - x) % n)
    if p < 2: p += n
    while not is_prime(p): p += n
    return p

def subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s, x = set(), 1
        for _ in range(n): s.add(x); x = x*h % p
        if len(s) == n: return sorted(s)
    raise RuntimeError

def energy(p, n):
    H = subgroup(p, n)
    cnt = Counter()
    for a in H:
        for b in H: cnt[(a+b) % p] += 1
    return sum(v*v for v in cnt.values())

print("KEYSTONE VERIFICATION: E_{F_p}(mu_n) vs claimed 3n(n-1), transfer threshold ~n^2.3\n")
for m in range(3, 8):
    n = 1 << m
    target = 3*n*(n-1)
    print(f"n={n}: claimed E = 3n(n-1) = {target}")
    for exp in [3.0, 2.6, 2.4, 2.3, 2.2, 2.1, 2.0]:
        p = prime_1_mod_n_ge(int(n**exp), n)
        E = energy(p, n)
        tag = "= 3n(n-1)  ✓" if E == target else f"SURPLUS +{E-target}"
        print(f"    p≈n^{exp:<4} = {p:>10}  E = {E:>8}   {tag}")
    print()

# Diagnostic: does the surplus correlate with a SMALL integer landing in mu_n?
print("\nMECHANISM CHECK: surplus vs small-element-in-subgroup (s in mu_n iff s^n=1 mod p)")
def smalls_in_mun(p, n):
    return [s for s in (2,3,5,6,7) if pow(s, n, p) == 1]
for (n, p) in [(32,4129),(32,3041),(64,9473),(64,6337),(128,70529),(128,43649),(16,337),(16,449)]:
    if (p-1) % n: continue
    H = subgroup(p, n)
    from collections import Counter
    c = Counter((a+b)%p for a in H for b in H)
    E = sum(v*v for v in c.values()); target = 3*n*(n-1)
    sm = smalls_in_mun(p, n)
    print(f"  n={n} p={p}: E={E} {'CLEAN' if E==target else f'+{E-target}'} | small ints in mu_n: {sm or 'none'} | E/n^2={E/n**2:.2f}")
