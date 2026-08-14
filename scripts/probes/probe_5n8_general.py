"""Probe (#444/#407): the structured single-line floor s*(2^mu, n/4) >= 5n/8 for ALL mu>=3.

At rate rho=1/4 (k = n/4 = 2^{mu-2}), the optimal spike e = floor(log2(k-1)) in the witness
(x^{n/2}+1)*(x^{2^e}-x0^{2^e}) gives sStarLowerBound = n/2 + 2^e. Claim: the optimizer is
e = mu-3 (the largest e with 2^e <= k-1 = 2^{mu-2}-1), giving n/2 + 2^{mu-3} = 5*2^{mu-3} = 5n/8,
for ALL mu>=3 (not just the n=8,16 decide cases already in FloorAsymptoticRadius).

NEVER n=q-1: this is the THIN 2-power subgroup mu_n, rho=1/4 fixed. Single-line s* (NOT delta*).
"""
import math

print("mu |    n | k=n/4 |  k-1 | e*=floor(log2(k-1)) | mu-3 | n/2+2^e* |  5n/8 | match")
ok = True
for mu in range(3, 22):
    n = 2 ** mu
    k = n // 4                # = 2^{mu-2}
    km1 = k - 1               # = 2^{mu-2} - 1
    estar = int(math.floor(math.log2(km1))) if km1 >= 1 else -1
    floor_val = n // 2 + 2 ** estar
    five_n_8 = 5 * n // 8
    e_claim = mu - 3
    spike_fits = (2 ** e_claim <= km1)
    estar_is_claim = (estar == e_claim)
    match = (floor_val == five_n_8) and spike_fits and estar_is_claim
    ok = ok and match
    print(f"{mu:2d} | {n:6d} | {k:5d} | {km1:4d} | {estar:18d} | {e_claim:3d} | {floor_val:7d} | {five_n_8:5d} | {match}")
print("ALL MATCH (e*=mu-3, floor=5n/8, spike fits):", ok)

print()
print("super-Johnson check: at rho=1/4, sqrt(kn)=n/2; 5n/8 > n/2 strictly:")
for mu in range(3, 9):
    n = 2 ** mu
    k = n // 4
    j = (k * n) ** 0.5
    print(f"  n={n:5d}: 5n/8={5*n//8:5d}  sqrt(kn)={j:7.1f}  super-Johnson={5*n//8 > j}")
