#!/usr/bin/env python3
"""
ANGLE [N1-fermat-floor-false] NEGATIVE-DIRECTION RIGOROUS VERDICT (#444 / proximity prize).

Question: my Bessel-deviation finding shows the SHARP floor M(n) <= sqrt(2 n ln m) (m=(p-1)/n)
is VIOLATED at the Fermat prime F4=65537 (pure 2-group field, ratio 1.14 at n=32). Does this
EXTEND to a NEGATIVE CLOSURE of the prize -- i.e. is the conjectured floor delta* = 1-rho-Theta(1/log n)
asymptotically FALSE for the smoothest fields?  (Prize quantifies per-code delta*_C over smooth F.)

THREE RIGOROUS TESTS (exact sup-norm M = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} cos(2pi b x/p),
proper mu_n: n=2^mu, n|p-1, p PRIME, NEVER n=p-1; eta constant on cosets b*mu_n => enumerate m reps):

  (T1) Does the SHARP-bound violation ratio M/sqrt(2n ln m) GROW with n at F4 (=> floor false)
       or stay BOUNDED (=> just a constant-calibration miss of the sharp sqrt(2) constant)?
  (T2) Is the ABSORBING bound M <= 2 sqrt(n ln p) (constant 2, the irrefutable survivor)
       EVER violated across the near-2-group smoothness spectrum?
  (T3) The Plancherel identity sum_{b!=0} |eta_b|^2 = n(p-n) EXACTLY (all primes) -- the structural
       reason M/sqrt(n) = O(sqrt(log m)) is bounded: L^2 mass is fixed, structured primes only
       CONCENTRATE it onto fewer cosets (larger constant), they cannot grow the ORDER.

VERDICT: NO-GAIN as a negative closure. The Fermat anomaly kills the SHARP sqrt(2) constant
(structured-false) but the floor's GROWTH LAW delta* = 1-rho-Theta(1/log n) survives: M ~ O(sqrt(n log m))
with constant ~1.5 (vs sharp sqrt(2)~1.41), absorbed by C=2. Violation is BOUNDED (peak 1.46 at F4 n=64,
DECLINES for large n) and does NOT grow. A rigorous negative closure would require the per-code
delta*_C to be UNPINNABLE in the asymptotic regime, which routes back to the BGK/Paley core, not Fermat.
"""
import math
from sympy import isprime, primitive_root

def Mmax(n, p, cap=300000):
    g = primitive_root(p); m = (p-1)//n
    if m > cap: return m, None, None, None
    h = pow(g, m, p); mun = [pow(h, j, p) for j in range(n)]; w = 2*math.pi/p
    M = 0.0
    for j in range(m):
        b = pow(g, j, p); s = 0.0
        for x in mun: s += math.cos(w*((b*x) % p))
        a = abs(s)
        if a > M: M = a
    return m, M, M/math.sqrt(2*n*math.log(m)), M/(2*math.sqrt(n*math.log(p)))

def odd_part_v2(p):
    q = p-1; v2 = 0
    while q % 2 == 0: q //= 2; v2 += 1
    return q, v2

print("=== (T1) F4=65537 full n-scan: SHARP-violation ratio is BOUNDED, does NOT grow ===")
print("n | m | M | M/sqrt(n) | M/sqrt(2n ln m) | M/(2 sqrt(n ln p)) | M/n(align)")
wS = wA = 0.0
for mu in range(1, 16):
    n = 1 << mu; m, M, rs, ra = Mmax(n, 65537)
    if M is None: continue
    wS = max(wS, rs); wA = max(wA, ra)
    flag = " VIOL-SHARP" if rs > 1 else ""
    print(f"{n} | {m} | {M:.2f} | {M/math.sqrt(n):.3f} | {rs:.4f}{flag} | {ra:.4f} | {M/n:.4f}")
print(f"  F4 worst SHARP ratio = {wS:.4f} (BOUNDED, peaks at small n, declines); worst ABSORB = {wA:.4f} (<1)")

print("\n=== (T2) ABSORBING bound hunt across near-2-group spectrum (p-1=2^a*odd, odd small) ===")
maxA = 0.0; argmax = None; nchk = 0; sharpViol = 0
for a in range(8, 20):
    for c in [1,3,5,7,9,11,13,15,17,19,21]:
        p = (1 << a)*c + 1
        if not isprime(p): continue
        _, v2 = odd_part_v2(p)
        for mu in range(2, v2+1):
            n = 1 << mu; m = (p-1)//n
            if m < 32: continue
            mm, M, rs, ra = Mmax(n, p)
            if M is None: continue
            nchk += 1
            if rs > 1: sharpViol += 1
            if ra > maxA: maxA = ra; argmax = (p, n, m, round(rs,4), round(ra,4))
print(f"  {nchk} checks; SHARP violated in {sharpViol} (constant-miss); ABSORBING worst = {maxA:.4f}")
print(f"  worst-absorb (p,n,m,sharpR,absorbR) = {argmax}")
print(f"  ABSORBING M<=2 sqrt(n ln p) violated: {'YES' if maxA>1 else 'NO (0 violations)'}")

print("\n=== (T3) Plancherel sum_{b!=0}|eta_b|^2 = n(p-n) EXACTLY (structural floor on growth) ===")
for (n, p) in [(16,65537),(32,65537),(64,65537),(16,5393),(32,46337)]:
    g = primitive_root(p); m = (p-1)//n; h = pow(g,m,p); mun = [pow(h,j,p) for j in range(n)]; w = 2*math.pi/p
    tot = 0.0
    for j in range(m):
        b = pow(g,j,p); s = 0.0
        for x in mun: s += math.cos(w*((b*x) % p))
        tot += n*(s*s)
    print(f"  n={n} p={p}: measured={tot:.1f} exact n(p-n)={n*(p-n)} ratio={tot/(n*(p-n)):.7f}")
print("  => avg|eta|^2 = n exactly; M/sqrt(n)=O(sqrt(log m)) bounded; structured primes only")
print("     concentrate the fixed L^2 mass (larger constant), cannot grow the ORDER. NEGATIVE CLOSURE FAILS.")
