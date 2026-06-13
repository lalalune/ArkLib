#!/usr/bin/env python3
"""Probe (#389 prize): the entropy closed-form ceiling delta* <= 1 - rho - H(rho)/log2(q*eps*).

N_fib(s,r) = C(s/2 - r%2, r//2) (proven in-tree TwoPowerFibreValue; probe-confirmed).
Unconditional ceiling: the explicit ladder family at dyadic level s=2^a gives
eps_mca >= N_fib(s,r)/q at radius delta = 1 - r/s, so delta is BAD when N_fib(s,r) > q*eps*.
We compare the exact best dyadic ceiling (in log-space, to avoid huge-integer blowup) to
the entropy closed form.
"""
from math import log2, sqrt, lgamma


def log2binom(n, k):
    """log2 C(n,k) via lgamma (n,k may be large)."""
    if k < 0 or k > n:
        return float("-inf")
    if k == 0 or k == n:
        return 0.0
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / log2(2.718281828459045)


def H(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * log2(p) - (1 - p) * log2(1 - p)


def main():
    print("delta*_ceiling: exact dyadic N_fib crossover (log-space)  vs  entropy 1-rho-H/L")
    print(f"{'rho':>7} {'L':>5} {'exact ceiling (s=2^a)':>24} {'entropy':>9} "
          f"{'Johnson':>9} {'cap':>7} win?")
    for rho in (0.5, 0.25, 0.125, 0.0625):
        for L in (40, 64, 128):
            best = None
            for a in range(2, 60):
                s = 2 ** a
                r = round(rho * s) + 2
                if r < 2 or r > s:
                    continue
                lognfib = log2binom(s // 2 - (r % 2), r // 2)
                if lognfib > L:      # N_fib > 2^L = q*eps*
                    delta = 1 - r / s
                    if best is None or delta < best[0]:
                        best = (delta, a)
            ent = 1 - rho - H(rho) / L
            jb, cap = 1 - sqrt(rho), 1 - rho
            bs = f"{best[0]:.5f} (a={best[1]})" if best else "none"
            inwin = best is not None and jb < best[0] < cap
            print(f"{rho:>7} {L:>5} {bs:>24} {ent:>9.5f} {jb:>9.4f} {cap:>7.4f}  {inwin}")
    print("\n'exact ceiling' = smallest BAD delta from explicit ladder family (unconditional")
    print("eps_mca lower bound); entropy formula 1-rho-H(rho)/L is its leading asymptotic.")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
