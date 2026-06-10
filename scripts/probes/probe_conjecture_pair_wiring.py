#!/usr/bin/env python3
"""Probe for the #302 pair-case conjecture wiring (falsify-first sanity check).

Claim being wired in Lean (pure composition of proven bricks):
    per-delta JohnsonNumericBound at eta := mu(delta)
      ==>  mca_johnson_bound_CONJECTURE at parl = Fin 2.
The one numerical content is the (already Lean-proven) comparison
    johnsonBoundReal(phi, 2^m, mu(delta).toNNReal, delta)
      <=  (card(Fin 2) - 1) * 2^(2m) / (q * (2*mu)^7)        -- conjecture errStar
with (card(Fin 2) - 1) = 1.  This probe re-checks the ORIENTATION of that
inequality (and that the (parl-1)=1 factor does not flip it) on a parameter grid,
so the Lean wiring cannot silently compose the comparison backwards.

johnsonBoundReal closed form (Hab25JohnsonArithmetic.johnsonBoundReal_eq):
  [ (2(M+1/2)^5 + 3(M+1/2)*delta*rho_plus) / (3*rho_plus^{3/2}) * n
    + (M+1/2)/sqrt(rho_plus) ] / q
with rho_plus = (k+1)/n, M = max(ceil(sqrt(rho_plus)/(2*eta)), 3), k = 2^m.
"""

import math

def check(n, m, q, delta):
    k = 2 ** m
    if k > n:
        return None
    rho = k / n
    sr = math.sqrt(rho)
    if not (0 < delta < 1 - sr):
        return None
    mu = min(1 - sr - delta, sr / 20)
    if mu <= 0:
        return None
    rho_plus = (k + 1) / n
    M = max(math.ceil(math.sqrt(rho_plus) / (2 * mu)), 3)
    P = M + 0.5
    jbr = ((2 * P**5 + 3 * P * delta * rho_plus) / (3 * rho_plus**1.5) * n
           + P / math.sqrt(rho_plus)) / q
    # conjecture errStar at parl = Fin 2: (2-1) * 2^(2m) / (q * (2*mu)^7)
    err_star = (2 - 1) * 2 ** (2 * m) / (q * (2 * mu) ** 7)
    return jbr, err_star

def main():
    total = 0
    violations = 0
    worst = None
    for m in range(2, 13):
        for log_blowup in (1, 2, 3, 4, 5):
            n = 2 ** (m + log_blowup)
            for q in (2**31 - 1, 2**64 - 59, 2**128 - 159, 2**16 + 1):
                sr = math.sqrt(2**m / n)
                for t in (0.05, 0.25, 0.5, 0.75, 0.95, 0.999):
                    delta = t * (1 - sr)
                    res = check(n, m, q, delta)
                    if res is None:
                        continue
                    jbr, err = res
                    total += 1
                    ratio = jbr / err if err > 0 else float("inf")
                    if jbr > err:
                        violations += 1
                        print(f"VIOLATION n={n} m={m} q={q} delta={delta:.4f}: "
                              f"jbr={jbr:.3e} > errStar={err:.3e}")
                    if worst is None or ratio > worst[0]:
                        worst = (ratio, n, m, q, delta)
    print(f"checked {total} parameter points; violations = {violations}")
    print(f"worst ratio johnsonBoundReal/errStar = {worst[0]:.3e} "
          f"at (n={worst[1]}, m={worst[2]}, q={worst[3]}, delta={worst[4]:.4f})")
    assert violations == 0, "comparison orientation is WRONG - do not wire"
    print("PASS: johnsonBoundReal <= conjecture errStar (parl=2) on the whole grid")

if __name__ == "__main__":
    main()
