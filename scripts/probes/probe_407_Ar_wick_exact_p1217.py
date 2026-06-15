import numpy as np
from sympy import isprime, primitive_root
from collections import Counter

# ADVERSARIAL re-verify A_2 > Wick_2 at n=32, p=1217 via EXACT integer arithmetic.
# E_r = #{(v,w) in (mu_n^r)^2 : sum v = sum w} (exact integer), A_r = E_r - n^{2r}/q.
n = 32
p = 1217
assert (p - 1) % n == 0 and isprime(p)
h = (p - 1) // n
g = primitive_root(p)
gen = pow(g, h, p)
mu = [pow(gen, j, p) for j in range(n)]
q = p

pair_sums = Counter()
for a in mu:
    for b in mu:
        pair_sums[(a + b) % p] += 1
E2 = sum(c * c for c in pair_sums.values())
A2 = E2 - (n ** 4) / q
Wick2 = 3 * (n ** 2)
print(f"n={n} p={p}: EXACT E_2={E2} (integer count)")
print(f"  A_2 = E_2 - n^4/q = {E2} - {n**4}/{q} = {A2:.4f}")
print(f"  Wick_2 = 3*n^2 = {Wick2}")
ok2 = A2 > Wick2
print(f"  A_2/Wick_2 = {A2/Wick2:.4f}  => {'VIOLATION CONFIRMED (exact)' if ok2 else 'no violation'}")

trip = Counter()
for a in mu:
    for b in mu:
        for c in mu:
            trip[(a + b + c) % p] += 1
E3 = sum(x * x for x in trip.values())
A3 = E3 - (n ** 6) / q
Wick3 = 15 * (n ** 3)
ok3 = A3 > Wick3
print(f"  EXACT E_3={E3}, A_3={A3:.2f}, Wick_3=15 n^3={Wick3}, A_3/Wick_3={A3/Wick3:.4f} => {'VIOL (exact)' if ok3 else 'no'}")
beta = np.log(p) / np.log(n)
print(f"  beta={beta:.3f} (THICK window). mu_n proper: n={n} < p-1={p-1}, |mu_n|={len(set(mu))}")
