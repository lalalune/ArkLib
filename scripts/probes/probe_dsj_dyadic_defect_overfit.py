#!/usr/bin/env python3
"""
probe_dsj_dyadic_defect_overfit.py

ADVERSARIAL test of the GPU-pinned formula and [AC2]/[AC8] (-2*depth defect).

The GPU "PERFECT fit n=8..32" is THREE data points: (8,?),(16,?),(32,?).
The model s*(n) = n/2 + 1 - 2*(log2 n - 3) has effectively the form
   s* = a*n + b*log2(n) + c
with 3 free-ish parameters (a=1/2 fixed by Johnson, b=-2, c=7). Fitting a
2-parameter line-in-(n,log2 n) to 3 points is a ZERO-residual fit by
construction (2 unknowns, but log2 n at n=8,16,32 are 3,4,5 = arithmetic, so
(n, log2 n) are NOT affinely independent enough?). Check rank / overfit.

Also: AC8 claims defect = 2 EXACTLY because width-4 minimal relation removes
one antipodal pair. Test the ALTERNATIVE simple hypotheses that ALSO fit
n=8,16,32 and ask which the GPU data (if extended) would distinguish.

DO NOT git commit.
"""
import numpy as np
from math import log2

def gpu_formula(n):
    return n/2 + 1 - 2*(log2(n)-3)

# The 3 validated points (back-computed from the stated formula since GPU values
# were given only via the formula; the claim is the formula FITS them perfectly).
pts = [(8, gpu_formula(8)), (16, gpu_formula(16)), (32, gpu_formula(32))]
print("Validated (claimed) points n=8,16,32:")
for n,s in pts: print(f"  n={n}  s*={s}")
print()

# Design matrix for model s = a*n + b*log2(n) + c  (3 params, 3 points => exact)
A = np.array([[n, log2(n), 1.0] for n,_ in pts])
y = np.array([s for _,s in pts])
print(f"rank of design matrix [n, log2 n, 1] on n=8,16,32: {np.linalg.matrix_rank(A)} (of 3)")
coef = np.linalg.solve(A, y)
print(f"  exact solve -> a={coef[0]:.4f} b={coef[1]:.4f} c={coef[2]:.4f}")
print("  => 3 points, 3 params: ANY such model fits exactly. Zero predictive power.")
print()

# Competing models that ALSO pass through n=8,16,32 exactly but DIVERGE at n>=64:
def m_gpu(n):  return n/2 + 1 - 2*(log2(n)-3)
def m_quad(n): # b*log2^2 variant tuned to same 3 pts
    A2 = np.array([[n, log2(n)**2, 1.0] for n,_ in pts]);
    c2 = np.linalg.solve(A2, y)
    return c2[0]*n + c2[1]*log2(n)**2 + c2[2]
def m_nlogn(n): # a*n + b*(n/log2 n) + c  tuned to same 3 pts
    A3 = np.array([[nn, nn/log2(nn), 1.0] for nn,_ in pts])
    c3 = np.linalg.solve(A3, y)
    return c3[0]*n + c3[1]*(n/log2(n)) + c3[2]

print("Extrapolation DIVERGENCE (these all fit n=8,16,32 perfectly):")
print(f"{'n':<6}{'gpu(-2*depth)':<16}{'log2^2 variant':<18}{'n/log2n variant':<18}")
for mu in range(3,11):
    n=2**mu
    print(f"{n:<6}{m_gpu(n):<16.3f}{m_quad(n):<18.3f}{m_nlogn(n):<18.3f}")
print()
print("VERDICT: n=8,16,32 (3 pts) CANNOT distinguish -2*depth from any other")
print("3-param model. The -2*(log2 n) claim is UNFALSIFIED by current data.")
print("Need GPU at n=64,128 to separate. delta* limit (->1/2) is identical for")
print("ALL models with leading term n/2, so 'recovers Johnson' is automatic and")
print("NOT evidence for the specific -2*depth defect.")
