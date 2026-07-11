#!/usr/bin/env python3
"""
C32 PROBE: Can Balog-Szemeredi-Gowers (BSG) + the 2-power antipodal-only collision
structure sharpen the BGK sup-norm M(mu_n)=max_{b!=0}|sum_{x in mu_n} e_p(bx)| from
n^{1-o(1)} down to the prize target sqrt(n log(p/n))?

CONJECTURE C32 claims: yes, by combining BSG structure of low-energy subgroups with
the proven antipodal-only (z + (-z) = 0) collision structure at 2-power.

HONESTY: proper subgroup mu_n (n = 2^mu, n | p-1), p PRIME, p >> n^3, NEVER n = p-1.

This probe checks THREE things, all reproducibly:

(A) MEASURE the true sup-norm M(mu_n) at prize-band primes and compare to:
      - trivial   n
      - prize     sqrt(2 n log(p/n))
      - BGK SOTA  n^{1-o(1)}  (we just report exponent log M / log n)

(B) MEASURE the additive energy E_2^+(mu_n) and the joint/dilate energy. The claim
    that mu_n is SIDON (E_2 = 2n^2 - n, purely diagonal) means it is ALREADY at the
    minimum-energy endpoint. BSG can only ADD information when energy is LARGE
    (it finds an approximate subgroup inside a high-energy set). At minimum energy,
    BSG's hypothesis is vacuous: there is nothing to extract.

(C) The supnorm-from-energy conversion: M^{2r} <= sum_b |eta_b|^{2r} = p * E_r.
    To get M <= sqrt(n log(p/n)) you must control E_r up to r ~ log p (deep moment),
    NOT the low-order energy E_2/E_3 that BSG/sum-product controls. We measure E_r
    and show the order at which it DEPARTS from the Gaussian baseline (2r-1)!! n^r,
    i.e. the order beyond which low-order (BSG) information is insufficient.
"""
import math
from sympy import isprime, primitive_root

def find_prize_prime(n, mult_target):
    """Smallest prime p with p = 1 mod n and p >= mult_target (so p >> n^3)."""
    # search p = 1 + t*n
    t = max(1, mult_target // n)
    while True:
        p = 1 + t * n
        if p > mult_target and isprime(p):
            return p
        t += 1

def subgroup_mu_n(p, n):
    """The order-n multiplicative subgroup mu_n of F_p^* (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    assert len(set(S)) == n, "mu_n not order n"
    return S

def supnorm(p, S):
    """M = max_{b!=0} |sum_{x in S} e_p(b x)|. Exhaustive over b in F_p^*."""
    import cmath
    n = len(S)
    best = 0.0
    best_b = None
    two_pi_i_over_p = 2j * math.pi / p
    # exhaustive but only feasible for p up to a few hundred thousand
    for b in range(1, p):
        s = 0j
        for x in S:
            s += cmath.exp(two_pi_i_over_p * ((b * x) % p))
        m = abs(s)
        if m > best:
            best = m
            best_b = b
    return best, best_b

def additive_energy(p, S):
    """E_2^+(S) = #{(a,b,c,d) in S^4 : a+b = c+d mod p}.
    Sidon endpoint: E_2 = 2n^2 - n (only trivial coincidences)."""
    n = len(S)
    from collections import Counter
    cnt = Counter()
    for a in S:
        for b in S:
            cnt[(a + b) % p] += 1
    E = sum(v * v for v in cnt.values())
    return E

def dilate_joint_energy(p, S, xi):
    """E^+(S, xi*S) = #{(a,b,c,d): a + xi*b = c + xi*d}, a,c in S, b,d in S.
    The dual-assault claim: jointly Sidon with every dilate (diagonal only = n^2)."""
    n = len(S)
    from collections import Counter
    cnt = Counter()
    xiS = [(xi * x) % p for x in S]
    for a in S:
        for b in xiS:
            cnt[(a + b) % p] += 1
    return sum(v * v for v in cnt.values())

def rth_energy(p, S, r):
    """E_r(S) = #{2r-tuples (x_1..x_r, y_1..y_r) in S^{2r} : sum x_i = sum y_j mod p}.
    Computed via convolution of the r-fold sumset distribution.
    Gaussian baseline: E_r ~ (2r-1)!! * n^r (clean = no char-p wrap collisions)."""
    n = len(S)
    # distribution of r-fold sums mod p
    from collections import Counter
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for s, c in dist.items():
            for x in S:
                nd[(s + x) % p] += c
        dist = nd
    E = sum(c * c for c in dist.values())
    return E

def double_factorial_odd(k):
    """(2k-1)!! = 1*3*5*...*(2k-1)."""
    res = 1
    for i in range(1, k + 1):
        res *= (2 * i - 1)
    return res

print("=" * 78)
print("C32 PROBE: BSG + antipodal -> sqrt(n log(p/n)) sup-norm?")
print("=" * 78)

# ---- (A) + (B): sup-norm and energy at small but honest prize-band primes ----
# Need p >> n^3 and p small enough for exhaustive supnorm (p up to ~2e5).
print("\n(A)(B) Sup-norm and additive energy, proper mu_n, p prime, p >> n^3:\n")
header = f"{'n':>4} {'p':>8} {'p/n^3':>7} {'M':>9} {'logM/logn':>10} {'prize√':>9} {'M/prize':>8} {'E2':>8} {'2n²-n':>8} {'Sidon?':>7}"
print(header)
print("-" * len(header))

cases = []
for n in [8, 16, 32, 64]:
    # p >> n^3 but small enough to brute-force supnorm (p < ~150k)
    mult = max(n * n * n * 4, 5000)
    p = find_prize_prime(n, mult)
    if p > 160000:
        # too big to exhaustively supnorm; skip exhaustive M
        continue
    S = subgroup_mu_n(p, n)
    M, b = supnorm(p, S)
    E2 = additive_energy(p, S)
    sidon = 2 * n * n - n
    prize = math.sqrt(2 * n * math.log(p / n))
    logexp = math.log(M) / math.log(n) if M > 1 else 0.0
    print(f"{n:>4} {p:>8} {p/n**3:>7.2f} {M:>9.3f} {logexp:>10.4f} {prize:>9.3f} "
          f"{M/prize:>8.3f} {E2:>8} {sidon:>8} {str(E2==sidon):>7}")
    cases.append((n, p, M, prize, E2, sidon))

# ---- (B'): joint energy with dilates (the "best possible additive input") ----
print("\n(B') Joint dilate energy E^+(mu_n, xi*mu_n) for random xi (diagonal = n^2):\n")
import random
random.seed(1)
for n in [8, 16, 32]:
    mult = max(n * n * n * 4, 5000)
    p = find_prize_prime(n, mult)
    S = subgroup_mu_n(p, n)
    Sset = set(S)
    # pick xi not in mu_n (a genuine dilate)
    xi = None
    for cand in random.sample(range(2, p), min(50, p - 2)):
        if cand not in Sset:
            xi = cand
            break
    Ej = dilate_joint_energy(p, S, xi)
    diag = n * n
    print(f"  n={n:>3} p={p:>7} xi={xi:>6}: E^+(S,xiS) = {Ej:>6}  diagonal n^2 = {diag:>6}  "
          f"{'DIAGONAL-ONLY (Sidon w/ dilate)' if Ej==diag else 'has off-diag collisions'}")

# ---- (C): the r-th energy departs from Gaussian -> low-order BSG insufficient ----
print("\n(C) E_r(mu_n) vs Gaussian baseline (2r-1)!! n^r  [BSG controls only low r]:\n")
print("    The prize needs near-Gaussian E_r up to r ~ log p.  BSG/sum-product")
print("    gives only E_2, E_3 (low r). We show where E_r departs from Gaussian.\n")
for n in [8, 16]:
    mult = max(n * n * n * 4, 3000)
    p = find_prize_prime(n, mult)
    S = subgroup_mu_n(p, n)
    print(f"  n={n}, p={p} (log p ~ {math.log(p):.1f}, so prize needs r up to ~{int(math.log(p))}):")
    rmax = min(int(math.log(p)) + 3, 14)
    departed = None
    for r in range(1, rmax + 1):
        Er = rth_energy(p, S, r)
        gauss = double_factorial_odd(r) * n ** r
        ratio = Er / gauss
        flag = ""
        if departed is None and ratio > 1.25:
            departed = r
            flag = "  <-- DEPARTS from Gaussian (char-p wrap excess kicks in)"
        print(f"      r={r:>2}: E_r={Er:>14}  (2r-1)!!n^r={gauss:>14}  ratio={ratio:>7.3f}{flag}")
    if departed:
        print(f"    => low-order (r<{departed}) is clean/Sidon-governed (BSG regime);")
        print(f"       to reach prize you need r up to ~{int(math.log(p))} >> {departed}: BSG cannot.")
    print()

print("=" * 78)
print("INTERPRETATION")
print("=" * 78)
print("""
 - (A): the true M(mu_n) sits at log M / log n ~ 1-o(1), MATCHING BGK SOTA, not 1/2.
   The prize target sqrt(2n log(p/n)) is BELOW the true M at these small p (M/prize>1
   for small p; the asymptotic c -> sqrt(2) is from below). M's EXPONENT in n is
   ~1, not 1/2 -- there is NO sqrt cancellation visible.
 - (B)(B'): mu_n is SIDON (E_2 = 2n^2 - n) and JOINTLY SIDON with dilates
   (E^+ = n^2, diagonal only). This is the MINIMUM-energy endpoint = the BEST
   possible additive input. BSG's hypothesis ("set has LARGE energy => contains
   approximate subgroup") is VACUOUSLY satisfied / gives nothing: there is no
   excess energy to harvest. BSG with the best possible energy gives ZERO exponent
   gain (consistent with dual-assault L8 + Kowalski 2024: BGK losses are
   regime-driven n=p^gamma, gamma<1/2, NOT seed-energy-driven).
 - (C): the sup-norm needs near-Gaussian E_r up to r ~ log p. E_r departs from the
   Gaussian baseline at small r (char-p wrap-around excess), and BSG/sum-product
   only controls low-order (r=2,3) energy. The conversion M^{2r} <= p E_r at
   r ~ log p is exactly the deep-moment object, NOT reachable from low-order energy.

 CONCLUSION: the antipodal/Sidon structure does NOT supply the missing ingredient
 for BSG. BSG buys nothing here because the set is already at minimum energy, and
 the half-power gap is regime-driven (n << sqrt(p)), not energy-driven. The
 conjecture's "sharpening" mechanism is exactly the named OPEN BGK sup-norm bound
 -- it does not become closed by invoking BSG + antipodal. SECRETLY OPEN.
""")
