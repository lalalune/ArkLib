#!/usr/bin/env python3
"""
probe_407_bhbi_house_threshold_sweep.py  (#407)

THE OPEN EDGE (left explicitly un-resolved by the BHBI-BIND bridge entry, 2026-06-15):
The realizable-BHBI / (BIND) failure at n=32 was established at p ~ n^4 ~ 2^20 prize-band primes
(8/8 had a height-1 vanishing relation Sum g_j omega^j = 0). BUT the sibling flagged the SCOPE caveat:

    "these primes are p~2^20, NOT the prize budget p~2^128. The house hypothesis (#S)^phi(32) < p is
     FALSE here ((#S)^16 ~ 2^51..59 >> 2^20). ... closing either at the prize budget needs the Sidon
     bootstrap."

So the existing n=32 "wall" lives ENTIRELY in the pigeonhole regime: there are 3^16 ~ 4.3e7 sign
vectors in {-1,0,1}^16 mapping into Z/p; a collision (=height-1 relation) is FORCED whenever
3^16 > p, i.e. p < ~4.3e7 ~ 2^25.4. Every n=32 prize-band prime tested (p~1.05e6 ~ 2^20) is DEEP
below this pigeonhole floor -- the relation is forced for ANY 16 distinct nonzero residues, thin
subgroup or not. It says NOTHING about thinness and NOTHING about the prize budget.

THE DECISIVE, UN-RUN QUESTION:
    Does the height-1 (and bounded-height) realizable BHBI relation PERSIST once p crosses the
    pigeonhole threshold p > 3^16, or does it VANISH? 
    - If it VANISHES (no relation once p large enough): the n=32 "break" is a pure small-p pigeonhole
      ARTIFACT. BHBI is ALIVE at the true prize budget. The lever is NOT walled -- the wall was a
      resolution artifact of testing at p~n^4 (far below the prize's effective p).
    - If it PERSISTS (relation survives past the pigeonhole floor, for the THIN subgroup, while a
      RANDOM 16-subset of residues stops having one): that is a GENUINE thin-structural obstruction
      -- the BHBI lever is truly walled by 2-power structure, independent of p.

This is the test that separates "artifact" from "structure". METHOD:
  Fix n=32, N=16 half-basis omega^j (omega primitive 32nd root, omega^16=-1). Sweep p UPWARD:
  p ~ 2^20 (forced) -> 2^24 -> 2^26 (~3^16 threshold) -> 2^28 -> 2^32 -> 2^36 -> 2^40 (well past floor).
  At each p: MITM for a minimal-height {-1,0,1} relation among the 16 thin half-basis powers (height 1),
  then height 2 ({-2..2}). CONTROL: same MITM on 16 RANDOM distinct nonzero residues (NOT a subgroup) at
  the same p -- isolates whether any surviving relation is THIN-SPECIFIC or generic.

Exact integer, no float. Proper thin 2-power subgroup mu_32 < F_p* (omega order verified == 32, never q-1).
Co-author: wakesync <shadow@shad0w.xyz>
"""
import sys, random
from itertools import product

def isprime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % q == 0: return x == q
    d = x-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(a, d, x)
        if v == 1 or v == x-1: continue
        for _ in range(r-1):
            v = v*v % x
            if v == x-1: break
        else:
            return False
    return True

def primitive_2pow_root(p, m):
    """primitive 2^m-th root of unity in F_p (order exactly 2^m). returns omega with omega^{2^{m-1}}=-1."""
    n = 1 << m
    if (p-1) % n != 0: return None
    e = (p-1)//n
    for base in range(2, min(p, 5000)):
        r = pow(base, e, p)
        if pow(r, n//2, p) == p-1 and pow(r, n, p) == 1:
            return r
    return None

def mitm_min_height(powers, p, hmax):
    """Min-height nonzero g in [-h,h]^N with sum g_j*powers_j == 0 (mod p), for h=1..hmax.
       Returns (height, g) or (None, None). MITM split halves."""
    N = len(powers)
    half = N // 2
    for h in range(1, hmax+1):
        rng = range(-h, h+1)
        # left table: residue -> left-vector (any one)
        left = {}
        for gl in product(rng, repeat=half):
            s = 0
            for j in range(half):
                if gl[j]: s = (s + gl[j]*powers[j]) % p
            if s not in left:
                left[s] = gl
        # right scan
        for gr in product(rng, repeat=N-half):
            s = 0
            for j in range(N-half):
                if gr[j]: s = (s + gr[j]*powers[half+j]) % p
            need = (-s) % p
            if need in left:
                g = left[need] + gr
                if any(x != 0 for x in g):
                    # confirm height is exactly h (not lower -- lower would've been found in earlier loop)
                    return h, g
    return None, None

def first_prime_band(m, target_bits, count):
    """primes p == 1 mod 2^m with p ~ 2^target_bits (so mu_{2^m} exists), ascending from 2^target_bits."""
    n = 1 << m
    lo = 1 << target_bits
    base = lo - (lo % n) + 1
    out = []; c = base
    while len(out) < count:
        if isprime(c) and (c-1) % n == 0:
            out.append(c)
        c += n
    return out

def main():
    m = 5; n = 32; N = 16
    pigeon_floor_bits = 16 * 1.585  # log2(3^16) ~ 25.36
    print("=== BHBI realizable-relation persistence vs the pigeonhole/house threshold (n=32, N=16) ===")
    print(f"# sign-vectors in {{-1,0,1}}^16 = 3^16 = {3**16} ~ 2^{pigeon_floor_bits:.2f}")
    print(f"# height-2 vectors {{-2..2}}^16 = 5^16 = {5**16} ~ 2^{16*2.322:.2f}")
    print("A height-1 relation is FORCED (pigeonhole) when p < 3^16 ~ 2^25.4.")
    print("PRIZE BUDGET is p ~ 2^128. We sweep p UPWARD through and PAST the floor.\n")
    print(f"{'p_bits':>7} | {'p':>14} | {'beta=log_n p':>12} | {'thin min-ht':>12} | {'random ctrl min-ht':>18}")
    print("-"*78)
    random.seed(1234567)
    sweep_bits = [20, 22, 24, 26, 28, 30, 32, 34, 36, 40]
    for tb in sweep_bits:
        ps = first_prime_band(m, tb, 1)
        if not ps: 
            print(f"{tb:>7} | (no prime found)"); continue
        p = ps[0]
        omega = primitive_2pow_root(p, m)
        if omega is None:
            print(f"{tb:>7} | {p:>14} | (no primitive 32nd root)"); continue
        # verify thin subgroup: order exactly 32, NOT q-1
        assert pow(omega, n, p) == 1 and pow(omega, n//2, p) == p-1, "omega order check"
        assert (p-1) != n, "must be proper subgroup (n != q-1)"
        powers = [pow(omega, j, p) for j in range(N)]   # thin half-basis 1,omega,...,omega^15
        h_thin, g_thin = mitm_min_height(powers, p, 2)
        # CONTROL: 16 random distinct nonzero residues (generic, NOT a subgroup) at same p
        rand_res = random.sample(range(1, p), N)
        h_rand, g_rand = mitm_min_height(rand_res, p, 2)
        beta = (tb * 0.30103) / (5 * 0.30103)  # log_n(p) = log2(p)/log2(32) = bits/5
        thin_s = f"h={h_thin}" if h_thin else ">2 (NONE)"
        rand_s = f"h={h_rand}" if h_rand else ">2 (NONE)"
        marker = ""
        if tb < pigeon_floor_bits and tb+2 > pigeon_floor_bits:
            marker = "  <-- pigeonhole floor"
        print(f"{tb:>7} | {p:>14} | {beta:>12.2f} | {thin_s:>12} | {rand_s:>18}{marker}")
        sys.stdout.flush()

    print("\nINTERPRETATION:")
    print("- If 'thin min-ht' becomes NONE (>2) once p_bits > ~26 (past 3^16 floor): the n=32 BHBI 'wall'")
    print("  was a PURE small-p PIGEONHOLE ARTIFACT. BHBI is ALIVE at the prize budget. Lever NOT walled.")
    print("- If 'thin min-ht' STAYS low (h<=2) while 'random ctrl' goes NONE: GENUINE thin-structural")
    print("  obstruction -> BHBI lever truly walled by 2-power structure independent of p.")
    print("- If BOTH stay low past the floor: relation is generic (any 16 residues), still artifactual.")

if __name__ == "__main__":
    main()
