#!/usr/bin/env python3
"""
FOLLOW-UP to probe_dyadic_geomean_asymptote.py.

First probe showed: the CUMULATIVE geomean rho_bar decreases with L but stays well above
sqrt(2) (~1.69 at n=128) AND above the prize-floor-slacked threshold in nearly every case.
The mechanism appears to be SATURATED BASE RUNGS: at small n the subgroup sum has NO
cancellation, M(n)=n exactly, so rho=2.0 for the first few doublings; cancellation only
sets in at deep n, too late to pull the geomean to sqrt(2).

This follow-up isolates the ASYMPTOTIC per-level ratio two ways, to decide ALIVE vs DEAD:

(A) TAIL geomean: geomean of rho_i over only the DEEP rungs (n >= 16), where cancellation is
    active. If even the tail geomean stays > sqrt(2), telescoping is dead regardless of the
    saturated base (REFUTATION, with the base-saturation as the named obstruction).

(B) The TRUE asymptotic question for the PRIZE floor. We do NOT need geomean <= sqrt(2). We
    need the WHOLE telescoped product to beat the prize floor:
        M(2^L) <= C * sqrt(2^L * log(p/n)).
    Equivalently the prize "headroom"
        H(n) := M(n) / sqrt(n * log(p/n))
    must stay BOUNDED (<= C). We measure H(n) directly along the tower (this is the prize
    constant itself). If H(n) is bounded/decreasing, the prize floor numerically HOLDS for
    these instances even though the geomean exceeds sqrt(2) -- proving the telescoping
    REDUCTION (geomean<=sqrt2) is STRICTLY STRONGER than the prize and was the wrong target,
    NOT that the prize fails. That is the precise, useful refinement of wf-A1's refutation.

PROBE-FIRST, PROPER mu_n, p>>n^3, NEVER n=q-1.
"""
import math
import numpy as np
from sympy import primitive_root, isprime


def subgroup(t, n, p):
    S = []
    x = 1 % p
    for _ in range(n):
        S.append(x)
        x = (x * t) % p
    return S


def M_of(n, p, g):
    t = pow(g, (p - 1) // n, p)
    S = subgroup(t, n, p)
    f = np.zeros(p, dtype=np.float64)
    f[S] = 1.0
    mags = np.abs(np.fft.fft(f))
    mags[0] = 0.0
    return float(mags.max())


def main():
    sqrt2 = math.sqrt(2.0)
    # (p, Lmax_exp, primitive_root precomputed to avoid slow sympy primitive_root on large p)
    cases = [(786433, 6, 10), (5767169, 7, 3), (7340033, 7, 3)]
    print("FOLLOW-UP: tail geomean + direct prize headroom H(n)=M(n)/sqrt(n log(p/n))")
    print("sqrt(2) =", round(sqrt2, 6))
    print()
    all_tail = []
    for p, Lmax_exp, g in cases:
        if not isprime(p):
            print(f"p={p} not prime, skip"); continue
        # verify g is a primitive root: g^((p-1)/r) != 1 for each prime r | (p-1)
        from sympy import factorint
        ord_ok = all(pow(g, (p - 1) // r, p) != 1 for r in factorint(p - 1))
        if not ord_ok:
            print(f"p={p}: g={g} not a primitive root, skip"); continue
        Ms = {}
        a = 1
        while a <= Lmax_exp and (p - 1) % (1 << a) == 0 and p > (1 << a) ** 3:
            Ms[a] = M_of(1 << a, p, g)
            a += 1
        levels = sorted(Ms)
        if len(levels) < 4:
            print(f"p={p}: short tower, skip"); continue
        print(f"=== p={p}  g={g}  n=2^{levels[0]}..2^{levels[-1]} ===")
        print("  n        M(n)     rho     H(n)=M/sqrt(n log(p/n))")
        rhos_deep = []
        for idx, i in enumerate(levels):
            n = 1 << i
            H = Ms[i] / math.sqrt(n * math.log(p / n))
            if idx >= 1:
                rho = Ms[i] / Ms[i - 1]
                if n >= 16:
                    rhos_deep.append(rho)
                print(f"  {n:<7d} {Ms[i]:8.4f} {rho:7.4f}  {H:8.4f}")
            else:
                print(f"  {n:<7d} {Ms[i]:8.4f}  (base)   {H:8.4f}")
        if rhos_deep:
            tail_gm = math.exp(sum(math.log(r) for r in rhos_deep) / len(rhos_deep))
            all_tail.extend(rhos_deep)
            print(f"  TAIL geomean (n>=16 rungs) = {tail_gm:.4f}   ({'>' if tail_gm>sqrt2 else '<='} sqrt2)")
        print()
    if all_tail:
        gm = math.exp(sum(math.log(r) for r in all_tail) / len(all_tail))
        print(f"POOLED tail geomean over all deep rungs = {gm:.4f}  (sqrt2={sqrt2:.4f})")
    print()
    print("INTERPRETATION:")
    print("  H(n) bounded/decreasing  => prize floor HOLDS numerically on these instances;")
    print("                              the geomean<=sqrt2 telescoping target is STRICTLY")
    print("                              STRONGER than the prize (wf-A1 refuted the strong target,")
    print("                              not the prize). Mechanism: base-rung saturation M(n)=n")
    print("                              (rho=2, no cancellation) permanently inflates the geomean.")
    print("  tail geomean still > sqrt2 => per-level descent never reaches sqrt2 even asymptotically;")
    print("                              telescoping-to-sqrt(n) is dead, INDEPENDENT of base saturation.")


if __name__ == "__main__":
    main()
