#!/usr/bin/env python3
"""Probe for SpectrumGFAlternatingSum.lean (#444).

Discharges Sweep_A50's asserted-but-unproven x=-1 "alternating sum" consequence.
A50 proved (x^2-1)*G(x) = x^(m+2)(x+2)^m - (2x+1)^m where
  G(x) = spectrumGF(x,m) = sum_k C(m,k) 2^k sum_{i<m-k+1} x^(k+2i).
At x=-1 the prefactor (x^2-1)=0 (removable singularity), so the value is NOT recoverable
by division -- it needs a DIRECT manifest-sum evaluation.

CLAIM (A50 header "(new here)"):  spectrumGF(-1, m) = (-1)^(m+1) * (m-1).

MECHANISM verified here:
  inner sum_i (-1)^(k+2i) = (-1)^k (m-k+1)
  => spectrumGF(-1,m) = sum_k C(m,k)(-2)^k (m-k+1)
                      = (m+1) sum_k C(m,k)(-2)^k - sum_k k C(m,k)(-2)^k
                      = (m+1)(1-2)^m - 2m(1-2)^m         [binomial + k-weight derivative id]
                      = (-1)^m (1-m) = (-1)^(m+1)(m-1).
"""
from math import comb

def spectrumGF(x, m):
    tot = 0
    for k in range(m + 1):
        inner = sum(x ** (k + 2 * i) for i in range(m - k + 1))
        tot += comb(m, k) * 2 ** k * inner
    return tot

def main():
    fails = 0
    N = 60
    for m in range(0, N + 1):
        v = spectrumGF(-1, m)
        claim = (-1) ** (m + 1) * (m - 1)
        # binomial GF at -2
        s1 = sum(comb(m, k) * (-2) ** k for k in range(m + 1))
        # k-weighted GF at -2
        s2 = sum(k * comb(m, k) * (-2) ** k for k in range(m + 1))
        kform = (m + 1) * s1 - s2
        ok = (v == claim) and (s1 == (-1) ** m) and (s2 == 2 * m * (-1) ** m) and (kform == v)
        if not ok:
            fails += 1
            print(f"FAIL m={m}: v={v} claim={claim} s1={s1} s2={s2} kform={kform}")
    print(f"alternating-sum spectrumGF(-1,m)=(-1)^(m+1)(m-1): {fails} fails / {N + 1} (m=0..{N})")
    print("mechanism (binomial (1-2)^m + k-weight 2m(-1)^m + inner-collapse): all verified")
    # m=0 edge: both sides = 1 (so the identity is UNCONDITIONAL, not just m>=1)
    print(f"m=0 edge: spectrumGF(-1,0)={spectrumGF(-1,0)} == (-1)^1*(0-1)={(-1)**1*(0-1)}")

if __name__ == "__main__":
    main()
