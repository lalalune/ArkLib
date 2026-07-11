#!/usr/bin/env python3
"""
Probe for #444: the char-0 subset-sum spectrum COEFFICIENT palindrome N_r = N_{2m-r}.

The x^r coefficient of spectrumGF (Sweep_A50) is, in closed form,
    N_r = sum_{k <= min(r, 2m-r),  k == r (mod 2)} C(m,k) * 2^k.
This probe confirms, BEFORE formalizing:
  [1] the palindrome N_r = N_{2m-r} for all r <= 2m (the depth-reflection symmetry);
  [3] the closed form equals the manifest GF coefficient (expand the double sum
      sum_k C(m,k) 2^k sum_{i<=m-k} x^{k+2i} and read off the x^r coefficient);
  [4] the two mechanism facts the Lean proof uses:
        parity   r == (2m-r) (mod 2)  [since 2m even], and
        cutoff   min(r, 2m-r) symmetric under r <-> 2m-r.

BOUNDARY NOTE (caught by this probe): for r > 2m the RAW closed form is NOT the GF
coefficient -- at even r > 2m the k=0 term survives (value 1 != 0). So the palindrome
is stated/proved only on its valid domain r <= 2m. (The Lean file documents this.)
"""
from math import comb


def Nr_closedform(m, r):
    if r < 0 or r > 2 * m:
        return 0
    top = min(r, 2 * m - r)
    return sum(comb(m, k) * (2 ** k) for k in range(top + 1) if k % 2 == r % 2)


def Nr_manifest_coeff(m):
    coeffs = {}
    for k in range(m + 1):
        c = comb(m, k) * (2 ** k)
        for i in range(m - k + 1):
            d = k + 2 * i
            coeffs[d] = coeffs.get(d, 0) + c
    return coeffs


def raw_closedform(m, r):
    top = min(r, max(2 * m - r, 0))
    return sum(comb(m, k) * (2 ** k) for k in range(top + 1) if k % 2 == r % 2)


def main():
    ok1 = all(
        Nr_closedform(m, r) == Nr_closedform(m, 2 * m - r)
        for m in range(40) for r in range(2 * m + 1)
    )
    print(f"[1] palindrome N_r = N_(2m-r), m=0..39: {'PASS' if ok1 else 'FAIL'}")

    ok3 = True
    for m in range(25):
        cf = Nr_manifest_coeff(m)
        for r in range(2 * m + 1):
            if cf.get(r, 0) != Nr_closedform(m, r):
                ok3 = False
    print(f"[3] closed form == manifest GF coefficient, m=0..24: {'PASS' if ok3 else 'FAIL'}")

    ok4 = all(
        ((2 * m - r) % 2 == r % 2) and (min(r, 2 * m - r) == min(2 * m - r, r))
        for m in range(30) for r in range(2 * m + 1)
    )
    print(f"[4] parity r==2m-r (2) + min symmetric: {'PASS' if ok4 else 'FAIL'}")

    # boundary: even r > 2m -> raw closed form keeps k=0 (=1), so NOT vacuous off-support
    boundary = raw_closedform(5, 12)  # r=12 > 2m=10, even -> k=0 term = 1
    print(f"[boundary] raw closed form at even r>2m (m=5,r=12) = {boundary} (expected 1, !=0)")

    assert ok1 and ok3 and ok4 and boundary == 1, "probe FAILED"
    print("ALL PASS")


if __name__ == "__main__":
    main()
