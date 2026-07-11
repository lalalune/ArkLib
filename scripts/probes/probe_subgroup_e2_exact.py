"""
PROBE: the EXACT r=2 energy of a genuine multiplicative subgroup mu_n subset F_p*.
Question: is it 2n^2 - n (additive count = Spec/p) or 3n^2 - 3n (Shaw's Wick-model 'anchor')?

For mu_n a multiplicative subgroup, the additive energy E_2 = #{(a1,a2,b1,b2) in mu_n^4 : a1+a2 = b1+b2}.
The TRIVIAL solutions are {a1,a2}={b1,b2} as multisets: gives 2n^2 - n (n^2 ordered pairs counted with the
diagonal a1=a2 once). EXTRA solutions exist when mu_n has additive structure (mu_n is NOT Sidon in F_p):
a1+a2=b1+b2 with {a1,a2}!={b1,b2}. So the REAL subgroup E_2 = 2n^2 - n + (extra), and extra > 0 generally
(the subgroup has additive coincidences). So E_2(mu_n) >= 2n^2 - n, and the generic-set value 2n^2-n is a
LOWER bound, NOT exact for the structured subgroup.

So at r=2: generic char-0 additive = 2n^2 - n; structured-subgroup additive = 2n^2 - n + extra(p,n);
Wick-model = 3n^2 - 3n. Let's measure all three at real prize-regime primes p >> n^3.
"""
import math
from collections import Counter

def subgroup(p, n):
    e = (p - 1) // n
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and len({pow(h, i, p) for i in range(n)}) == n:
            return [pow(h, i, p) for i in range(n)]
    return None

def add_energy_modp(S, p, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[(v + x) % p] += m
        c = nc
    return sum(m * m for m in c.values())

def isprime(m):
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return m > 1

def find_prime(n, beta_target_cube=True):
    # find prime p with n | p-1 and p >> n^3
    base = n ** 4
    p = base + 1
    while True:
        if isprime(p) and (p - 1) % n == 0:
            return p
        p += 1

print("r=2 subgroup energy: generic(2n^2-n) vs actual subgroup additive vs Wick-model(3n^2-3n):")
for n in [4, 8, 16]:
    p = find_prime(n)
    S = subgroup(p, n)
    if S is None:
        print(f"  n={n} p={p}: no subgroup found"); continue
    E2 = add_energy_modp(S, p, 2)
    generic = 2 * n * n - n
    wickmodel = 3 * n * n - 3 * n
    extra = E2 - generic
    print(f"  n={n:>2} p={p}: E2(subgroup)={E2:>6}  generic(2n^2-n)={generic:>6}  Wick-model(3n^2-3n)={wickmodel:>6}  extra={extra}")
print()
print("INTERPRETATION:")
print(" - 2n^2-n = generic/Sidon char-0 additive E_2 (the all-distinct + single-collision count).")
print(" - actual subgroup E_2 = 2n^2-n + extra (extra from mu_n's additive coincidences, NOT Sidon).")
print(" - 3n^2-3n (Shaw's anchor) = (2*2-1)!!*(n)_2 = WICK-MODEL, the independent-pairing reference.")
print("   It is NOT the literal subgroup E_2 unless extra happens to equal n^2-2n (coincidence).")
