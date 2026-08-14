#!/usr/bin/env python3
"""
Probe: the SMALLEST SPLIT (prize-regime, p ≡ 1 mod n) prime admitting an antipodal-free subset
of μ_n that VANISHES IN THE PRIME FIELD F_p (g ∈ F_p, not just F̄_p).

The prize regime is p ≡ 1 mod n (q·ε* ≈ n), where the primitive n-th root g lives in F_p, so only
in-F_p vanishings feed the char-p energy E_r. The non-split p=3 witness (SpurWeightThreeCollision)
has g ∈ F_9 \ F_3 — outside the prize regime. This finds the prize-faithful witness.

Result (exact, F_p, proper μ_n, n=2^m, NEVER n=q-1):
- m=3 (n=8): NO split prime p ≡ 1 mod 8 (≤2e5) has any antipodal-free weight-3/4 subset vanishing
  in F_p. The prize-regime Spur is empty for these weights at m=3.
- m=4 (n=16): p=17 (≡1 mod 16, SPLIT, 17 ≡ 1 mod 4 = surviving Chebotarev class) has {0,1,4}
  antipodal-free with 1+g+g^4=0 in F_17 (g=3, ord 16). FIRST prize-regime spurious collision.
  => Spur_2(17) ≥ 1 in the split regime. Formalized in SpurSplitPrizeRegime.lean.
"""
from sympy import primerange
from itertools import combinations

def find_split_collision(m, maxp=200000):
    n = 2**m
    for p in primerange(n+1, maxp):
        if (p-1) % n != 0:
            continue
        g = None
        for a in range(2, p):
            if pow(a, n, p) == 1 and pow(a, n//2, p) == p-1:
                g = a; break
        if g is None:
            continue
        pw = [pow(g, i, p) for i in range(n)]
        half = n//2
        for w in [3, 4]:
            for sub in combinations(range(n), w):
                if any((sub[i]-sub[j]) % n == half for i in range(w) for j in range(w)):
                    continue
                if sum(pw[i] for i in sub) % p == 0:
                    return (p, g, sub, w)
    return None

if __name__ == "__main__":
    for m in [3, 4]:
        r = find_split_collision(m)
        print(f"m={m} n={2**m}: smallest split prime p≡1 mod {2**m} with antipodal-free subset "
              f"vanishing in F_p: {r}")
