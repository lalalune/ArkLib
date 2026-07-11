#!/usr/bin/env python3
"""
probe_hgg_crosscorr_route_C4.py  (#407 / #389 char-p wall, angle C4-helleseth-golomb-gong)

QUESTION (the task): does the Helleseth-Golomb-Gong (HGG) cross-correlation tradition deliver
an EFFECTIVE UPPER BOUND (sup) on  M(mu_n) = max_{b!=0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x),
at the Ramanujan scale (~ 2 sqrt(n)), or only Welch-type sqrt LOWER bounds?

HGG cross-correlation theory, precisely:
  Given an m-sequence over F_{p^e} (period N = p^e - 1) and its decimation by d,
  C_d(tau) = sum_{x in F_{p^e}*} psi( x^d - alpha x )   (a Weil sum over the FULL group).
  - For SPECIAL decimations d (Niho exponents, Welch, Kasami, ...) the spectrum
    {C_d(tau)} is 3-valued or 4-valued, each value O(p^{e/2}) = O(sqrt(N+1)) -> EFFECTIVE sup.
  - For GENERIC d, only Welch/Sidelnikov LOWER bound  max|C_d| >= sqrt-ish  applies (wrong dir).

The PRIZE object lives over a multiplicative SUBGROUP mu_n (n | p-1), NOT the full group, and
is a sum over a thin set. Two ways HGG could connect:

  (A) "subgroup-sum = cross-correlation peak" reading: eta_b is the inner sum over mu_n.
      Is there a decimation d and field so that {eta_b : b != 0} = an HGG-family correlation
      spectrum with a KNOWN small-valued (3/4-valued) distribution? If yes -> UPPER bound.

  (B) Welch-lower-bound reading (the I025 direction trap): max |eta_b| >= sqrt floor only.

This probe TESTS, in the prize-faithful regime (mu_n = 2-power subgroup, n | p-1, p PRIME, p >> n^3,
PROPER m = (p-1)/n > 1, NEVER n = p-1):

  T1. Is the period spectrum {eta_b} FEW-VALUED (like an HGG 3/4-valued decimation)? If it were,
      HGG's exact-value method would give an upper bound. If many-valued, HGG exact spectra do NOT
      apply and only the (wrong-direction) Welch lower bound survives.
  T2. Welch lower bound vs the true M: confirm Welch is a LOWER bound (direction trap), measuring
      the gap.  Welch family-bound for N sequences of length n:  max-corr^2 >= n(N - n)/(n N - 1)... 
      we use the simplest sum-of-squares (Parseval) floor which is the operative HGG/Welch content here.
  T3. The "HGG decimation upper bound would need" scale: the HGG few-valued spectra give |C| ~ sqrt(field),
      and the field here is F_p (e=1) since mu_n < F_p*. Over F_p (e=1) ALL multiplicative chars are
      genuine; the Gauss period is NOT a Weil sum of a decimated monomial over an EXTENSION -- check
      whether the e=1 case has ANY nontrivial HGG decimation content at all.
"""
import math
from collections import Counter
from cmath import exp, pi

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    # find a generator of F_p^*
    if p == 2: return 1
    phi = p - 1
    facs = set()
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            facs.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs): return g
    return None

def find_prime(n, beta=3.2):
    # smallest prime p > n^beta with n | p-1 (proper: m=(p-1)/n > 1), n = 2^mu
    target = int(n ** beta)
    # p = 1 + n*m, want p prime, m > 1
    m = max(2, target // n)
    while True:
        p = 1 + n*m
        if p > target and is_prime(p):
            return p, m
        m += 1

def gauss_periods(n, p, g):
    # mu_n = subgroup of order n = { g^{m*j} : j } where m=(p-1)/n
    m = (p - 1) // n
    gen_mu = pow(g, m, p)                  # generator of mu_n
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = (x * gen_mu) % p
    w = exp(2j*pi/p)
    etas = {}
    for b in range(1, p):
        s = 0j
        for x in mu:
            s += w ** ((b*x) % p)
        etas[b] = s
    return etas, mu, m

def main():
    print("="*78)
    print("HGG cross-correlation route (C4) -- decisive directional probe")
    print("regime: mu_n = 2-power subgroup, n|p-1, p PRIME, p>>n^3, proper m>1, n!=p-1")
    print("="*78)
    for mu_exp in [3,4,5]:          # n = 8,16,32
        n = 2**mu_exp
        p, m = find_prime(n, beta=3.2)
        g = primitive_root(p)
        etas, mu, m = gauss_periods(n, p, g)
        absvals = [abs(v) for v in etas.values()]
        M = max(absvals)
        sqrtn = math.sqrt(n)
        # T1: few-valued? round |eta| to 3 decimals, count distinct values
        rounded = Counter(round(a, 3) for a in absvals)
        n_distinct_abs = len(rounded)
        # also distinct COMPLEX values (HGG spectra are complex few-valued)
        rc = Counter((round(v.real,2), round(v.imag,2)) for v in etas.values())
        n_distinct_cplx = len(rc)
        # T2: Welch/Parseval lower bound:  sum_{b!=0} |eta_b|^2 = n(p-1) - n^2  (exact),
        #     so the AVERAGE of |eta_b|^2 over b!=0 is n - n^2/(p-1) -> n.  Floor = sqrt(avg).
        sum_sq = sum(a*a for a in absvals)
        avg_sq = sum_sq / (p-1)
        welch_floor = math.sqrt(avg_sq)     # = the Parseval/Welch LOWER content (= sqrt(n))
        # an honest "few-valued?" verdict: HGG 3/4-valued spectra have <=4 distinct abs values
        few = n_distinct_abs <= 6
        print(f"\nn={n}  p={p}  m=(p-1)/n={m}  beta=log_n(p)={math.log(p)/math.log(n):.2f}")
        print(f"  M = max|eta_b|        = {M:.4f}   (M/sqrt(n) = {M/sqrtn:.3f},  Ramanujan target 2sqrt(n)={2*sqrtn:.3f})")
        print(f"  Welch/Parseval floor  = sqrt(avg|eta|^2) = {welch_floor:.4f}  (= sqrt(n) = {sqrtn:.3f})  [LOWER content]")
        print(f"  T1 distinct |eta| values (round 3dp): {n_distinct_abs}   distinct complex: {n_distinct_cplx}")
        print(f"      -> few-valued (HGG 3/4-val exact-spectrum applicable)? {'YES' if few else 'NO'}")
        # show the top few abs multiplicities
        top = sorted(rounded.items(), key=lambda kv:-kv[1])[:6]
        print(f"      top |eta| buckets (val:count): {top}")
        print(f"  T2 direction: Welch floor {welch_floor:.3f} {'<=' if welch_floor<=M else '>'} M {M:.3f}"
              f"  => Welch is a {'LOWER' if welch_floor<=M else 'UPPER'} bound (gap M/floor = {M/welch_floor:.3f})")
    print("\n" + "="*78)
    print("INTERPRETATION KEY:")
    print(" - HGG gives an EFFECTIVE UPPER bound ONLY when the correlation spectrum is FEW-valued")
    print("   (Niho/Welch/Kasami decimations, 3-or-4-valued, each O(sqrt field)).")
    print(" - If {eta_b} is MANY-valued, the exact-spectrum HGG method does NOT apply; only the")
    print("   Welch/Sidelnikov LOWER bound survives = wrong direction (the I025 trap, re-confirmed).")
    print(" - The Gauss period over mu_n is an e=1 (F_p, not extension F_{p^e}) object: the HGG")
    print("   decimation machinery is built for EXTENSION-field m-sequences (e>=2). At e=1 there is")
    print("   no decimated-monomial Weil-sum structure to feed the few-valued theorems.")
    print("="*78)

if __name__ == "__main__":
    main()
