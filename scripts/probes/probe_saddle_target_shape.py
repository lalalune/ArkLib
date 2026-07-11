#!/usr/bin/env python3
"""
PROBE (rule 2) for the saddle TARGET-shape companion brick (#444 §6.2).

CoshMGFSaddleFloorShape lands ||eta_{b0}|| <= (3/sqrt2)*sqrt(n*log q), CONDITIONAL on the open MGF
inequality.  The PRIZE TARGET form is C*sqrt(n*log(q/n)).  In the prize regime q = n^beta we have
  log q       = beta * log n
  log(q/n)    = (beta-1) * log n          (q/n = n^(beta-1), needs beta>1, n>=2)
so   sqrt(n*log q) = sqrt(beta/(beta-1)) * sqrt(n*log(q/n)).

CLAIM to verify (so it composes into the literal prize target shape):
  For beta >= 2 and n >= 2 (so q = n^beta, q/n = n^(beta-1) >= n >= 2, log(q/n) > 0):
     sqrt(n * log q)  <=  sqrt(2) * sqrt(n * log(q/n)).
  i.e. log q <= 2*log(q/n), i.e. beta <= 2*(beta-1), i.e. beta >= 2.  Tight at beta=2.

Then chaining gives the TARGET-shape floor with absolute constant
     C_target = (3/sqrt2) * sqrt(2) = 3.
  ||eta_{b0}|| <= 3 * sqrt(n * log(q/n))      (conditional on the open MGF inequality).

We verify BOTH:
 (A) the ratio identity sqrt(n*logq)/sqrt(n*log(q/n)) = sqrt(beta/(beta-1)) exactly, and
 (B) sqrt(beta/(beta-1)) <= sqrt(2) for beta >= 2 (the uniform constant, tight at beta=2),
 (C) the composed bound (3/sqrt2)*sqrt(n*logq) <= 3*sqrt(n*log(q/n)) over a grid (0 violations).
ASYMPTOTIC GUARD: this is a positive SHAPE of a CONDITIONAL floor (inherits the open MGF hyp),
NO beyond-Johnson/capacity claim, cliff-at-n/2 untouched.  NON-MOMENT real-analytic arithmetic.
"""
import math

def check():
    viol_B = 0
    viol_C = 0
    tot = 0
    worst_ratio = 0.0
    # prize regime beta in [2,6], n = 2^a (proper 2-power thin subgroups), a=4..10
    betas = [2.0, 2.0001, 2.3, 3.0, 4.0, 4.5, 5.0, 5.5, 6.0]
    for beta in betas:
        for a in range(4, 11):
            n = 2 ** a
            q = n ** beta
            logq = math.log(q)
            logqn = math.log(q / n)        # = (beta-1)*log n
            assert logqn > 0
            # (A) ratio identity
            ratio = math.sqrt(n * logq) / math.sqrt(n * logqn)
            ident = math.sqrt(beta / (beta - 1))
            assert abs(ratio - ident) < 1e-9, (beta, a, ratio, ident)
            worst_ratio = max(worst_ratio, ratio)
            # (B) uniform constant sqrt(2)
            if ratio > math.sqrt(2) + 1e-12:
                viol_B += 1
            # (C) composed target-shape bound with C_target = 3
            lhs = (3 / math.sqrt(2)) * math.sqrt(n * logq)
            rhs = 3 * math.sqrt(n * logqn)
            if lhs > rhs + 1e-9:
                viol_C += 1
            tot += 1
    print(f"(A) ratio identity sqrt(beta/(beta-1)): verified exact, 0 mismatches / {tot}")
    print(f"(B) ratio <= sqrt(2) for beta>=2: {viol_B} violations / {tot}  (worst ratio {worst_ratio:.6f}, sqrt2={math.sqrt(2):.6f})")
    print(f"(C) (3/sqrt2)*sqrt(n logq) <= 3*sqrt(n log(q/n)): {viol_C} violations / {tot}")
    # tightness at beta=2
    print(f"tightness check beta=2: sqrt(beta/(beta-1)) = {math.sqrt(2/1):.6f} = sqrt2 (TIGHT)")
    # the pure inequality reduction: logq <= 2 log(q/n)  <=>  beta <= 2(beta-1)  <=>  beta>=2
    print("reduction: sqrt(n logq) <= sqrt2 sqrt(n log(q/n))  <=>  logq <= 2 log(q/n)  <=>  beta>=2  [TIGHT at beta=2]")
    assert viol_B == 0 and viol_C == 0
    print("ALL CHECKS PASS. C_target = (3/sqrt2)*sqrt2 = 3, uniform over beta>=2, tight at beta=2.")

if __name__ == "__main__":
    check()
