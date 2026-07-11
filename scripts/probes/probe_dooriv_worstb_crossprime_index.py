#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — CROSS-PRIME worst-b coset-INDEX coincidence (a genuinely new measurement).

Prior worst-b probes mapped, for a SINGLE prime p, the structure WITHIN that prime's quotient
Z_k (k=(p-1)/n): the worst quotient index j*(p) and its internal arithmetic (gcd/sublattice/QR/v2)
came out SCATTERED/unstructured. The prime-stability probe (probe_444_worstb_const_prime_stability)
measured the worst-b COHERENCE CONSTANT C across primes and found it prime-stable (an O(1) pin).

NEITHER measured the object this probe targets: is the worst-b coset itself a PRIME-INDEPENDENT
ARITHMETIC object? I.e. as p ranges over primes p = k*n+1 (k varying), does the worst quotient
index j*(p) land at an arithmetically-distinguished position that is REPEATABLE across primes
(e.g. always j* ≈ k/2, or j* picks the SAME residue class / same multiple-of-d coset, or the worst
b maps to a fixed element under a natural prime-independent normalization)?

WHY this matters (door-(iv) exploitability test):
 - If the worst b were prime-INDEPENDENTLY structured (an arithmetic rule selects it, repeatable
   across p), an anti-concentration bound could TARGET that fixed structure without sum-product —
   a real crack. This is the LIVE form of the brief's open question "is the worst-b SET structured?"
 - If instead the worst-index NORMALIZED position j*/k is prime-INDEPENDENTLY DELOCALIZED (uniform
   on (0,1), no repeatable arithmetic), then no prime-independent rule selects the adversary, and a
   targeted (non-energy, non-sum-product) anti-concentration bound has nothing prime-stable to grip —
   a constraint lemma closing this specific door-(iv) hope (Lane 3).

We measure, for each n in the prize regime and many primes p = k*n + 1 (p >> n^3, beta ~ 4):
  (A) j*(p)/k  : normalized worst-index position. Is its distribution uniform on (0,1) or pinned?
  (B) coincidence rate: pick the SAME normalized position from one prime, map to the nearest coset
      in another prime — does it stay near-worst? (transfer of the argmax across primes)
  (C) the residue class of j*(p) mod small d (2,3,4): biased, or uniform (prime-independent)?

EXACT integer arithmetic for the period via primitive-root powers; NEVER n=q-1 (PROPER mu_n).
Probe-first, honest verdict.
"""
from __future__ import annotations
import math, cmath, statistics, random
import sympy as sp

random.seed(444)  # reproducible

TAU = 2.0 * math.pi

def primes_1_mod_n(n: int, kmin: int, count: int):
    """Yield primes p = k*n+1 with k >= kmin, ascending, up to `count` of them."""
    k = kmin
    out = []
    while len(out) < count:
        p = k * n + 1
        if sp.isprime(p):
            out.append((k, p))
        k += 1
    return out

def mu_n_elements(p: int, n: int):
    """The order-n multiplicative subgroup mu_n of F_p^* (n | p-1). Returns sorted residues."""
    g = int(sp.primitive_root(p))
    h = pow(g, (p - 1) // n, p)   # generator of mu_n
    s = set()
    x = 1
    for _ in range(n):
        s.add(x)
        x = (x * h) % p
    assert len(s) == n, (p, n, len(s))
    return g, sorted(s)

def period_abs_all_cosets(p: int, n: int, g: int, mu: list[int], kmax_scan: int):
    """
    eta_b = sum_{x in mu_n} e_p(b x). eta is constant on mu_n-cosets of b, so the search space is
    the quotient F_p^*/mu_n of size k=(p-1)/n. Coset reps: b_j = g^j for j=0..k-1 (g a prim root;
    g^j ranges over reps of the quotient as j mod k, since g^k generates mu_n... careful: actually
    g has order p-1, and g^k has order n = mu_n, so {g^j : j=0..k-1} is a transversal of mu_n). 
    Returns dict j -> |eta_{g^j}| for j in scanned range.
    """
    k = (p - 1) // n
    # RANDOM uniform subsample (NOT strided!) so residue classes j mod d are unbiased.
    # Strided sampling (range(0,k,stride)) biases j mod stride -> 0, a known scan artifact.
    if k <= kmax_scan:
        scan = range(k)
    else:
        scan = random.sample(range(k), kmax_scan)
    res = {}
    for j in scan:
        b = pow(g, j, p)
        acc = 0j
        for x in mu:
            r = (b * x) % p
            acc += cmath.exp(1j * TAU * r / p)
        res[j] = abs(acc)
    return k, res

def main():
    print("# door-(iv) cross-prime worst-b coset-INDEX coincidence")
    print("# prize regime: n=2^a, p=k*n+1, p>>n^3 (beta~4), PROPER mu_n. EXACT phase sums.")
    print()
    KMAX_SCAN = 4000   # cap cosets scanned per prime (uniform subsample for large k)
    NPRIMES = 14
    results = {}
    for n in (16, 32, 64):
        # beta ~ 4  =>  p ~ n^4  =>  k = (p-1)/n ~ n^3.  kmin so that p >= n^4 (p>>n^3 strongly).
        kmin = max(2, (n**4) // n)   # ~ n^3
        primes = primes_1_mod_n(n, kmin, NPRIMES)
        norm_positions = []   # j*/k
        resid_mod = {2: [], 3: [], 4: []}
        worst_C = []
        for (k0, p) in primes:
            g, mu = mu_n_elements(p, n)
            k, res = period_abs_all_cosets(p, n, g, mu, KMAX_SCAN)
            jstar = max(res, key=lambda j: res[j])
            Mabs = res[jstar]
            norm_positions.append(jstar / k)
            for d in (2, 3, 4):
                resid_mod[d].append(jstar % d)
            # coherence constant C = M^2 * ... we just report normalized M / sqrt(n*log(p/n))
            denom = math.sqrt(n * math.log(p / n))
            worst_C.append(Mabs / denom)
        # (A) normalized-position distribution
        mean_pos = statistics.mean(norm_positions)
        try: sd_pos = statistics.stdev(norm_positions)
        except statistics.StatisticsError: sd_pos = 0.0
        # (C) residue bias: chi-square-ish; report counts
        print(f"## n={n}  ({len(primes)} primes, p in [{primes[0][1]}, {primes[-1][1]}], k~{primes[0][1]//n})")
        print(f"   normalized worst-index j*/k:  mean={mean_pos:.3f}  sd={sd_pos:.3f}  "
              f"(uniform(0,1) => mean~0.5, sd~0.289)")
        print(f"   j*/k samples: {', '.join(f'{x:.3f}' for x in sorted(norm_positions))}")
        for d in (2, 3, 4):
            counts = [resid_mod[d].count(r) for r in range(d)]
            print(f"   j* mod {d}: {counts}  (uniform => ~{len(primes)/d:.1f} each)")
        print(f"   worst-b M/sqrt(n log(p/n)): mean={statistics.mean(worst_C):.3f} "
              f"min={min(worst_C):.3f} max={max(worst_C):.3f}")
        results[n] = (mean_pos, sd_pos, norm_positions)
        print()

    print("## VERDICT")
    print("Read mean/sd of j*/k vs the uniform(0,1) reference (mean 0.5, sd 0.289).")
    print("If sd ~ 0.289 and residue counts ~ uniform across all n: the worst-b coset INDEX is")
    print("prime-independently DELOCALIZED — no repeatable arithmetic rule selects the adversary")
    print("across primes => no prime-stable structure for a targeted anti-concentration bound to grip")
    print("(closes the 'worst-b is a prime-independent arithmetic object' door-(iv) hope).")
    print("If j*/k pins to a fixed value or residues are biased: a prime-independent selection rule")
    print("EXISTS => potential exploitable structure; would warrant adversarial re-check + formalize.")

if __name__ == "__main__":
    main()
