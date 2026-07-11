#!/usr/bin/env python3
"""
wf407 / B3-s128 — Q2: does the Myerson/Lehmer lacunary-cyclotomic-resultant route
open s=128 WITHOUT Thorner-Zaman?

The Myerson/Lehmer angle (357-T13): sharp upper bounds on |Res(f, Phi_k)| for lacunary
+-1 / sparse f would TIGHTEN the resultant bound M, hence LOWER the bad-prime budget and
the explicit threshold p > M.

But our budget analysis (wf407_B3-s128_verdict.py) showed the budget is NOT what gates the
prize s=128 -- the asymptotic supply n^{b-1} dwarfs ANY polynomial-in-n budget. So a tighter
M from Myerson/Lehmer:
  (a) helps the EXPLICIT-THRESHOLD / census route (p > M): improves unconditional coverage,
      but only up to |F| < 2^{const} -- it does NOT make the prime POLYNOMIAL in n.
  (b) does NOT help the POLYNOMIAL-FIELD route: that needs a prime to EXIST in [n^b, 2n^b],
      which is a prime-EXISTENCE question (TZ), orthogonal to how big M is.

Let me quantify (a): how far does the BEST possible resultant bound push the explicit
threshold, and is it ever polynomial in n?

Best-case resultant bound for a sparse +-1 poly f of L1-norm <= 2r over Phi_{2^m}:
  - trivial:    |f(zeta)| <= 2r => |Res| <= (2r)^{phi} = (2r)^{2^{m-1}}
  - Parseval:   sum |f(zeta)|^2 = 4n => AM-GM => |Res|^2 <= 8^{phi} => |Res| <= 2^{3n/4}
  - Mahler/Landau: |Res| <= 2^{deg} M(f)^{phi}, M(f) <= ||f||_2 = sqrt(#terms)
  - ABSOLUTE FLOOR: |Res(f,Phi_k)| >= 1 (nonzero integer). The MINIMUM is 1.
    A *good* prime must divide NO resultant, so it suffices that p does not divide a product
    of resultants of total log-size B. The threshold route needs p > max|Res|, i.e. p > M.
"""
from math import comb, log2

print("="*100)
print("Q2: the Myerson/Lehmer route -- best-possible resultant bound vs polynomiality in n")
print("="*100)
print("For the EXPLICIT-THRESHOLD route p > M to give a POLYNOMIAL prime p = n^b,")
print("we would need log2(M) <= b * log2(n).  At prize scale n ~ 2^{2^mu}, log2(n) = 2^mu.")
print()
print(f"{'s=2^mu':>8} {'log2 n':>8} {'r(rho=1/2)':>11} {'log2 M_triv':>12} {'log2 M_pars':>12} "
      f"{'b for M_pars':>13} {'poly?':>6}")
for mu in [5,6,7,8]:
    s=2**mu; h=2**(mu-1); log2n=2**mu
    r=s//2
    log2_M_triv = h*log2(2*r)
    log2_M_pars = 0.75*s
    # smallest b such that b*log2 n >= log2 M_pars
    b_needed = log2_M_pars/log2n
    poly = "YES" if b_needed<=10 else "no"   # poly means b is a fixed constant
    print(f"{s:>8} {log2n:>8} {r:>11} {log2_M_triv:>12.1f} {log2_M_pars:>12.1f} "
          f"{b_needed:>13.3f} {poly:>6}")

print()
print("KEY: at prize scale, log2 n = 2^mu = s. So b_needed = log2(M_pars)/log2 n = (3s/4)/s = 0.75.")
print("That means p > M_pars is satisfied by p ~ n^{0.75}... but WAIT: p must be >= n (since")
print("p == 1 mod n needs p > n). And the supply/window is [n^b, 2n^b] with b >= 1 anyway.")
print()
print("So at prize scale, the EXPLICIT-THRESHOLD p > M_pars (=2^{3s/4}=n^{3/4}) is *automatically*")
print("met by ANY p > n (since b>=1 > 3/4)!  The Parseval bound is ALREADY polynomial-compatible.")
print()
print("="*100)
print("THE REAL POINT (reconciliation of s=64 unconditional vs s=128 needs TZ):")
print("="*100)
print("""
There are TWO different 's' thresholds being conflated in the census literature:

(A) CENSUS / TOWER-CLOSURE route (char-0 -> char-p transfer of vanishing-sum structure):
    needs p > M = resultant bound, with FIXED small field |F| < 2^256.
    - coarse M = (2^m)^{2^{m-1}}: p > 2^{m*2^{m-1}}; at m=7: p > 2^448 > 2^256 => FAILS at |F|<2^256.
    - Parseval M = (2^m)^{2^{m-2}} (or 2^{3n/4}): halves exponent; at m=7: p > 2^224 < 2^256 => OK.
    => THIS is what 'Parseval opened s=64 uncond / extends census to n=128 at |F|<2^256' means.
       It is a CENSUS-COVERAGE statement (does the char-p tower close), NOT the KKH26 ceiling.

(B) KKH26 LEMMA-2 POLYNOMIAL-FIELD route (the actual delta* ceiling at p = Theta(n^b)):
    needs a prime p == 1 mod n to EXIST in [n^b, 2n^b] avoiding all collision resultants.
    - The avoidance is FREE: bad budget ~ poly(n) << supply ~ n^{b-1} (proven above, both M).
    - The ONLY gate is: does the supply n^{b-1-o(1)} EXIST?  = [TZ24] PNT-in-AP, b > 12/5.
    => THIS is the 's=128 needs Thorner-Zaman' statement. It does NOT depend on the resultant
       bound at all. Parseval/Landau/Myerson-Lehmer CANNOT help here.

CONCLUSION on Q2: Myerson/Lehmer lacunary resultant maxima help route (A) (sharper M =>
unconditional census coverage at smaller fields) but CANNOT open route (B) -- the polynomial
prime-EXISTENCE is orthogonal to the resultant size. The Myerson/Lehmer route is therefore
NOT a viable substitute for Thorner-Zaman in the KKH26 polynomial-field ceiling.
""")
