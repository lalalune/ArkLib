#!/usr/bin/env python3
"""
Probe for CONJECTURE [C12]: Stepanov Auxiliary at Convolution Depth.

C12 claims: the Stepanov auxiliary on the r-fold product curve gives
    #{mu_n r-fold collision} = E_r(mu_n) <= (2r-1)!! * n^r * (1 + 2^r r! / sqrt(q))
hence M(mu_n) <= sqrt(2 n log(p/n)) PAST Johnson at depth r = log(p/n).

E_r(G) = #{(x_1..x_r, y_1..y_r) in G^{2r} : sum x_i = sum y_i}
       = sum_s c_s^2   where c_s = #{r-tuples summing to s}.

This is the SAME object as GaussPeriodMomentBound.GaussianEnergyBound:
    E_r(mu_n) <= (2r-1)!! n^r   (the char-0 "real-Gaussian" bound).

We test, over PROPER subgroups mu_n (n=2^mu, n|p-1, p prime, p >> n^3, NEVER n=p-1):
  (1) char-0 reference: does E_r match (2r-1)!! n^r asymptotically (it is an UPPER bound)?
  (2) char-p: does E_r(mu_n in F_p) STAY <= (2r-1)!! n^r, or is there a FORCED ANOMALY
      E_r^{Fp} > E_r^{char0} that breaks C12's count once r grows?
  (3) THE DECISIVE TEST: even granting the count, the moment bound on M is
        M <= (q * E_r)^{1/2r}.
      We compute the BEST achievable M-bound over all r and compare to:
        - the trivial floor n,
        - the Johnson-equivalent sqrt(n) [the sqrt-cancellation Ramanujan target],
        - C12's claimed sqrt(2 n log(p/n)).
      The MomentMethodNoGo theorem (in-tree) proves (q E_r)^{1/2r} >= n ALWAYS.
      We verify this numerically: the moment bound NEVER drops below n.

Honesty: exact integer enumeration of E_r over the actual subgroup in F_p.
"""
import sympy
from itertools import product
from math import isqrt, log, prod

def doublefac(m):
    # (2r-1)!! for m = 2r-1
    r = 1
    k = m
    while k > 0:
        r *= k
        k -= 2
    return r

def subgroup(p, n):
    # mu_n = {x : x^n = 1} in F_p^*, n | p-1
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of order n
    S = []
    cur = 1
    for _ in range(n):
        S.append(cur)
        cur = (cur*h) % p
    assert len(set(S)) == n, "subgroup wrong size"
    return S

def energy_r(S, p, r):
    """E_r = sum_s c_s^2, c_s = #{r-tuples from S summing to s mod p}."""
    counts = {}
    for tup in product(S, repeat=r):
        s = sum(tup) % p
        counts[s] = counts.get(s, 0) + 1
    return sum(c*c for c in counts.values())

def energy_r_char0(S_int, r, modulus=None):
    """Same but treating S as plain integers (char-0 surrogate: no wraparound)."""
    counts = {}
    for tup in product(S_int, repeat=r):
        s = sum(tup)
        counts[s] = counts.get(s, 0) + 1
    return sum(c*c for c in counts.values())

print("="*100)
print("C12 PROBE: Stepanov auxiliary at convolution depth -> E_r(mu_n) <= (2r-1)!! n^r past Johnson?")
print("="*100)

# Use small-enough mu so r-fold enumeration is tractable: n=8 (r up to 4), n=16 (r up to 3).
cases = [(8, 25609), (16, 204913)]

for n, p in cases:
    mu = n.bit_length()-1
    S = subgroup(p, n)
    print(f"\n### mu_n: n=2^{mu}={n}, p={p} (prime, p/n^3={p/n**3:.1f}, n != p-1={n!=p-1})")
    print(f"{'r':>2} | {'E_r(Fp)':>14} | {'(2r-1)!! n^r':>16} | {'ratio E/bound':>13} | {'(q E_r)^(1/2r)':>15} | {'vs n':>8} | {'vs sqrt(n)':>10}")
    rmax = 4 if n == 8 else 3
    sqrtn = n**0.5
    for r in range(1, rmax+1):
        Er = energy_r(S, p, r)
        gauss = doublefac(2*r-1) * n**r
        ratio = Er / gauss
        Mbound = (p * Er) ** (1.0/(2*r))
        print(f"{r:>2} | {Er:>14} | {gauss:>16} | {ratio:>13.4f} | {Mbound:>15.2f} | {Mbound/n:>8.3f} | {Mbound/sqrtn:>10.3f}")

print("\n" + "="*100)
print("KEY: 'vs n' column = Mbound/n. MomentMethodNoGo proves this is ALWAYS >= 1.")
print("     C12 needs Mbound ~ sqrt(2 n log(p/n)) << n. The 'vs sqrt(n)' col shows how far above sqrt(n) we are.")
print("     If Mbound/n >= 1 for ALL r, the moment/energy route (incl. C12's count) CANNOT reach sub-Johnson.")
print("="*100)

# ============================================================================
# PART 2: The arithmetic of C12's headline claim sqrt(2 n log(p/n)).
# C12 minimizes M_r = (q (2r-1)!! n^r)^{1/2r} over r, optimum r* ~ log q.
# BUT the CharPMomentRecursion/MomentMethodNoGo floor forces E_r >= n^{2r}/q.
# These two are INCOMPATIBLE for large r: (2r-1)!! n^r >= n^{2r}/q  requires
#   (2r-1)!! >= n^r / q, i.e. the Gaussian ceiling can only be BELOW the trivial
#   n^{2r} ceiling while ABOVE the CS floor n^{2r}/q.  Check where the
#   "Gaussian" ceiling would have to hold to give sub-Johnson, vs the prize r*.
# ============================================================================
import math
print("\n" + "="*100)
print("PART 2: C12 headline arithmetic.  Prize: n=2^30, q=n*2^128 => log2(q)=158, ln q ~ 109.5.")
print("="*100)

def lg(x): return math.log2(x)

n_prize = 2**30
q_prize = n_prize * 2**128
lnq = math.log(q_prize)
# C12 optimum r* ~ ln q ; the Gaussian min M = sqrt(2 n ln q)
r_star = lnq
M_gauss = math.sqrt(2 * n_prize * lnq)
print(f"\nGRANTING the char-0 Gaussian bound E_r <= (2r-1)!! n^r at r*=ln q ~ {r_star:.1f}:")
print(f"  claimed M = sqrt(2 n ln q) = {M_gauss:.3e},  n = {n_prize:.3e},  M/n = {M_gauss/n_prize:.4f}  (sub-Johnson if <1) ")
print(f"  This is the SAME headline as GaussPeriodMomentBound.lean.  The bound IS sub-Johnson IF the")
print(f"  char-0 energy bound transfers to r*=ln q ~ {r_star:.0f}.")

print(f"\nTHE CHAR-p TRANSFER WALL (the hidden open step):")
print(f"  Lam-Leung char-0 bound E_r <= (2r-1)!! n^r transfers to F_p ONLY when no nonzero")
print(f"  <=2r-term +/-1 combination of 2^mu-th roots vanishes mod p, i.e. q > (2r)^(phi(n)) = (2r)^(n/2).")
mu = 30
phin = n_prize // 2  # phi(2^30) = 2^29
# need q > (2r)^{n/2}: take log
# log2 q = 158 ; need 158 > (n/2) log2(2r) = 2^29 * log2(2 r*)
needed_log2 = phin * math.log2(2*r_star)
print(f"  At prize n=2^30: need log2(q) > phi(n)*log2(2r*) = 2^29 * log2(2*{r_star:.0f}) = {needed_log2:.3e}")
print(f"  Actual log2(q) = {lg(q_prize):.0f}.   {lg(q_prize):.0f} >> {needed_log2:.2e}?  -> {lg(q_prize) > needed_log2}")
print(f"  => char-p transfer FAILS by ~{needed_log2/lg(q_prize):.2e}x.  The Gaussian bound is")
print(f"     UNAVAILABLE in char p at the prize r*; it holds only for n < ~2 ln q/ln ln q ~ 40.")

# C12's specific count: weil_form_card_lt over r-fold product curve. The degree budget D = r q/2,
# vanishing M = n^{r-1}.  Check: the Stepanov counting gives |V| M < D, i.e.
#   |V| < D/M = (r q/2)/n^{r-1}.  For this to bound E_r meaningfully it must beat trivial n^{2r}/q-ish.
print("\n" + "="*100)
print("PART 3: C12's actual Stepanov count |V|*M < D with D = r q/2, M = n^{r-1}.")
print("  Gives |V| < D/M = (r q / 2) / n^{r-1}.  Is this even an UPPER bound on E_r below trivial?")
print("="*100)
for (n, p) in [(8, 25609), (16, 204913)]:
    print(f"\n n={n}, q=p={p}:")
    for r in range(1, 4):
        D = r * p / 2
        M = n**(r-1)
        V_bound = D / M
        trivial_Er = n**(2*r)  # trivial E_r ceiling
        print(f"  r={r}: D/M = {V_bound:.2f},  trivial n^2r = {trivial_Er},  Weil count {'beats' if V_bound < trivial_Er else 'WORSE than'} trivial")
