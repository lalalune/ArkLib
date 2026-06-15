"""
wf407 / T24-pfree : the p-free invariant c_r = E_r^infty / (r! * n^r).

GOAL (3 parts, per the thread):
(1) Verify c_r is EXACTLY p-free at several primes, compute it, relate to
    Bessel I0(2x)^{n/2} coefficients.
(2) Attempt the bridge: does a bound on c_r transfer to a char-p concentration
    bound uniformly in p?  Identify exactly where char-p defect (E_r - E_r^inf >= 0)
    re-enters and breaks p-uniformity.
(3) Decide: genuine new lever, or re-label of the char-0 -> char-p transfer wall?

Definitions (consistent with in-tree RungBesselEnergy.lean / EnergyCharacterTransport.lean):
  mu_n = the n-th roots of unity (n = 2^a in prize).
  In a field F_q with mu_n present (q = 1 mod n), eta_b = sum_{x in mu_n} psi(b x),
  psi a fixed nontrivial additive char.  Parseval: sum_b |eta_b|^{2r} = q * E_r,
  with the 2r-fold additive energy
     E_r(F_q) = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_i  (in F_q) }.

  CHAR-0 ("infinity") value: count solutions with the equation holding over C
  (equivalently over Z[zeta_n], i.e. as roots-of-unity vanishing sums), NOT mod p:
     E_r^inf = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_i  in C }.
  This is exactly the diagonal coefficient of |I0|-type generating fn; the
  in-tree besselCoeff gives E_r^inf = (2r)! * besselCoeff(n/2, r) ... we check the
  precise normalization numerically below.

c_r := E_r^inf / (r! * n^r).
"""

import itertools
from math import factorial, comb
from fractions import Fraction

# ---------- char-0 energy by exact roots-of-unity vanishing-sum counting ----------
# We work in Z[zeta_n] via integer vectors of exponents.  A sum
#   sum_{i} zeta^{a_i} - sum_j zeta^{b_j} = 0 in C
# iff, writing the multiplicity vector m in Z^n (m_k = #a's at k - #b's at k),
# the polynomial sum_k m_k X^k is divisible by the n-th cyclotomic-ish relation:
# over C, sum_k m_k zeta^k = 0 iff Phi_d | (sum m_k X^k) for every d | n with the
# right primitive structure.  Cleanest exact test: numerically with high precision is
# risky; instead use the EXACT criterion: sum_k m_k zeta_n^k = 0  <=>  (X^n - 1) and
# the integer poll... Simpler & exact for our scale: evaluate via the field Q(zeta_n)
# represented by reducing mod the n-th cyclotomic minimal structure.  For n a power
# of 2, zeta_n satisfies zeta^{n/2} = -1, and {1, zeta, ..., zeta^{n/2 - 1}} is a
# Q-basis (degree phi(n) = n/2).  So reduce exponents mod n using zeta^{n/2} = -1:
#   zeta^k = (-1)^{k // (n/2)} * zeta^{k mod (n/2)}   for n = 2^a.
# Then sum_k m_k zeta^k = 0  iff  all n/2 basis coefficients are 0.  EXACT integer test.

def char0_zero_pow2(exps_plus, exps_minus, n):
    """Exact test (n a power of 2): does sum zeta^a - sum zeta^b = 0 in C?"""
    half = n // 2
    coeff = [0] * half
    for a in exps_plus:
        sign = -1 if (a // half) % 2 else 1
        coeff[a % half] += sign
    for b in exps_minus:
        sign = -1 if (b // half) % 2 else 1
        coeff[b % half] -= sign
    return all(c == 0 for c in coeff)

def E_r_char0_pow2(n, r):
    """Exact char-0 (over C) 2r-fold additive energy of mu_n, n a power of 2."""
    rng = range(n)
    cnt = 0
    for xs in itertools.product(rng, repeat=r):
        for ys in itertools.product(rng, repeat=r):
            if char0_zero_pow2(xs, ys, n):
                cnt += 1
    return cnt

# ---------- char-p energy by exact counting in F_p ----------
def find_prime_with_roots(n, lo):
    """Smallest prime p >= lo with p = 1 mod n."""
    p = lo + ((1 - lo) % n)
    if p < lo:
        p += n
    while True:
        if p > 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            return p
        p += n

def roots_of_unity_mod_p(n, p):
    """The n distinct n-th roots of unity in F_p (p = 1 mod n)."""
    # find a generator of the subgroup of order n
    g = None
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1
                                        for q in prime_factors(n)):
            g = cand
            break
    roots = [pow(g, i, p) for i in range(n)]
    assert len(set(roots)) == n
    return roots

def prime_factors(n):
    fs = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d); n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return fs

def E_r_char_p(n, r, p):
    """Exact char-p 2r-fold additive energy of mu_n in F_p (p = 1 mod n)."""
    roots = roots_of_unity_mod_p(n, p)
    cnt = 0
    for xs in itertools.product(roots, repeat=r):
        sx = sum(xs) % p
        for ys in itertools.product(roots, repeat=r):
            if sum(ys) % p == sx:
                cnt += 1
    return cnt

# ---------- Bessel coefficient (matches in-tree besselCoeff) ----------
def antidiagonal_tuples(d, total):
    """All m: (m_0..m_{d-1}) in N^d with sum = total."""
    if d == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in antidiagonal_tuples(d - 1, total - first):
            yield (first,) + rest

def besselCoeff(d, r):
    s = Fraction(0)
    for m in antidiagonal_tuples(d, r):
        prod = Fraction(1)
        for mi in m:
            prod *= Fraction(1, factorial(mi) ** 2)
        s += prod
    return s

def gaussianCoeff(d, r):
    s = Fraction(0)
    for m in antidiagonal_tuples(d, r):
        prod = Fraction(1)
        for mi in m:
            prod *= Fraction(1, factorial(mi))
        s += prod
    return s

# ==================================================================
print("=" * 70)
print("PART 1: c_r p-free? compute it; relate to Bessel coefficients")
print("=" * 70)

for n in [4, 8]:
    print(f"\n--- n = {n} (mu_n = {n}-th roots of unity) ---")
    rmax = 4 if n == 4 else 3
    for r in range(1, rmax + 1):
        Einf = E_r_char0_pow2(n, r)
        # char-p at two different primes, in the "clean" regime (p large enough)
        p1 = find_prime_with_roots(n, 200)
        p2 = find_prime_with_roots(n, 2000)
        Ep1 = E_r_char_p(n, r, p1)
        Ep2 = E_r_char_p(n, r, p2)
        # the candidate p-free invariant
        cr = Fraction(Einf, factorial(r) * n ** r)
        # Bessel relation: E_r^inf =? (2r)! * besselCoeff(n/2, r)
        bc = besselCoeff(n // 2, r)
        Einf_from_bessel = factorial(2 * r) * bc
        gauss = factorial(2 * r) * gaussianCoeff(n // 2, r)  # = (2r-1)!! n^r
        print(f"  r={r}: E_r^inf={Einf:>8}  E_p({p1})={Ep1:>8}  E_p({p2})={Ep2:>8}"
              f"  | char0==p? {Einf==Ep1==Ep2}")
        print(f"        c_r = E_r^inf/(r! n^r) = {cr} = {float(cr):.4f}"
              f"   (Bessel pred E_r^inf = (2r)!*besselCoeff = {Einf_from_bessel}"
              f"  match={Einf_from_bessel==Einf})")
        dd = factorial(2 * r) // (factorial(r) * 2 ** r)  # (2r-1)!!
        print(f"        clean/Gaussian E_r^G = (2r-1)!! n^r = {dd*n**r} ; "
              f"c_r^Gauss = (2r-1)!!/(r! ... ) ratio E_r^inf/E_r^G = "
              f"{float(Fraction(Einf, dd*n**r)):.4f}")
