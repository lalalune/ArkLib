#!/usr/bin/env python3
"""probe_dsj_orbit_budget_crossing (#444)

Adversarial test of J1 + D-cluster: is the worst-direction over-det far-line
incidence I(c) = z + (n/2)*O(c), and does the budget crossing I<=n (i.e. O<=2)
land at agreement s* = n/2 + 1 - 2*(log2 n - 3) [GPU fit] rather than the pure
Johnson 2k-1?

We work char-0 / exactly over Q(zeta_n) by computing, for a far MONOMIAL direction
on mu_n (n=2^mu, rho=1/4 => k=n/4), the number of close codewords on the worst line
and the orbit count O, using a cyclotomic-faithful surrogate.

We do NOT have the GPU engine here; instead we test the ARITHMETIC IDENTITY that
J1/D depend on, against the published fit, to see whether the claimed mechanism
(O = RS list size, crosses 2 at Johnson + integer dyadic defect) is even
self-consistent. If the only "fit" is the offset constant 2-2(mu-3), we check
whether that defect equals the Lam-Leung antipodal parity quantum (D1): the number
of odd-degree readout channels deleted across mu_n > mu_{n/2} > ... > mu_8.
"""
import math

def fit_sstar(n):
    mu = int(round(math.log2(n)))
    return n//2 + 1 - 2*(mu - 3)

def johnson_agreement_int(n, rho=0.25):
    # sqrt(rho)*n
    return int(round(math.sqrt(rho)*n))

def k_of(n, rho=0.25):
    return int(round(rho*n))

print("=== Consistency of J1 leading term vs GPU fit ===")
print(f"{'n':>4} {'fit_s*':>7} {'sqrt(rho)n':>10} {'2k-1':>5} {'fit-Jagree':>11} {'fit-(2k-1)':>11}")
for mu in range(3, 9):
    n = 2**mu
    fs = fit_sstar(n)
    ja = johnson_agreement_int(n)
    k = k_of(n)
    print(f"{n:>4} {fs:>7} {ja:>10} {2*k-1:>5} {fs-ja:>+11} {fs-(2*k-1):>+11}")

print()
print("=== D-cluster: is defect = -2 * (#dyadic octaves mu_n>...>mu_8) ? ===")
# tower depth = number of octave STEPS from n down to 8 = mu - 3
print(f"{'n':>4} {'octaves(mu-3)':>13} {'-2*octaves':>10} {'fit-(2k-1)':>11} {'fit-(n/2)':>9} {'1-2(mu-3)':>9}")
for mu in range(3, 9):
    n = 2**mu
    oc = mu - 3
    fs = fit_sstar(n)
    k = k_of(n)
    print(f"{n:>4} {oc:>13} {-2*oc:>10} {fs-(2*k-1):>+11} {fs-(n//2):>+9} {1-2*oc:>+9}")

print()
print("=== Orbit-budget arithmetic (wf-D6): I=z+(n/2)O, I<=n  <=>  O<=2 (z<=1) ===")
# Verify the pure arithmetic the Lean file proves, then see what s* this forces
# IF O = generic Johnson list size (RS): O<=2 first at agreement sqrt(rho)*n.
# The fit says s* != sqrt(rho)*n exactly; so O cannot be the *generic* Johnson cap.
# Test: does the integer defect mean O crosses 2 at a DYADICALLY shifted radius?
for mu in range(3, 9):
    n = 2**mu
    half = n//2
    # at s*, claim is O = 2 (boundary). Then I = z + half*2 = z+n. Needs z=0 to fit <=n.
    # so the crossing is the largest s with O(s)>=3 (bad) -> O drops to 2 at s*+1? sign matters.
    # Just report the would-be I at O=2,3:
    print(f"n={n:>4}: O=2 -> I={half*2} (=n, boundary, z must be 0); O=3 -> I={half*3} (> n, bad)")

print()
print("=== delta* asymptotics ===")
print(f"{'n':>5} {'delta*=1-fit/n':>14} {'1/2-1/n':>9} {'+2(mu-3)/n':>11}")
for mu in range(3, 12):
    n = 2**mu
    fs = fit_sstar(n)
    d = 1 - fs/n
    print(f"{n:>5} {d:>14.5f} {0.5-1/n:>9.5f} {2*(mu-3)/n:>11.5f}")
