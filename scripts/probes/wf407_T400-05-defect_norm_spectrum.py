#!/usr/bin/env python3
# wf407_T400-05-defect_norm_spectrum.py
#
# Thread T400-05-defect (#407 prize). VERDICT-DRIVING probe.
#
# Prior work (docs/kb/deltastar-407-e2zero-modq-defect.md) established:
#   (i)  q-spread of N(n,w;F_q) IS the mod-q additive-energy defect k_D (two-signed:
#        DROP=saturation, RISE=halo carriers);
#   (ii) carrier-onset law:  S is a halo carrier mod q  <=>  q | N(e_2(S)),
#        N(alpha)=Res(Phi_n, alpha) the cyclotomic field norm of alpha=e_2(S).
#
# OPEN RESIDUAL flagged there (the lever for a verdict):
#   "the magnitude of the LARGEST N(e_2(S)) over window sets is the real lever,
#    NOT the per-q average. Is the defect distribution predictable/bounded, or does
#    it inherit the structured-prime explosion?"
#
# THIS PROBE answers that directly by computing the FULL carrier-norm spectrum.
#
# Key questions:
#   Q1. The archimedean ceiling (CyclotomicNormDefectThreshold) says for alpha a signed
#       sum of <=C unit-modulus terms, |N(alpha)| <= C^{phi(n)}. e_2(S) has C(w,2) terms,
#       each a root of unity, so C = C(w,2). Is the LARGEST realized |N(e_2(S))| close to
#       this ceiling (=> norm is "as big as a generic short vector", controllable) or does
#       structure make it MUCH smaller / push special primes (structured-prime explosion)?
#   Q2. What is the set of "carrier primes" (prime divisors q=1 mod n of some N(e_2(S)))?
#       Is it a thin/predictable set, or does it spray across all residue classes (=
#       every large prime is a carrier => the wall is uncontrollable)?
#   Q3. Worst-case-over-q amplification: at the adversarial q* = (a divisor of the largest
#       N), how big is the carrier count vs a generic q? Does the adversary get a
#       Theta(N(char0))-order count (= the whole list explodes) or only O(1)?
#   Q4. Does the largest realizable norm GROW with n in a way that reaches prize scale
#       (q ~ n*2^128)?  i.e. is there an alpha=e_2(S) with N(alpha) of prize magnitude?
#
# EXACT numerics (full enumeration; no sampling).  Run:  python <thisfile>

import itertools
from math import comb, log2
from sympy import isprime, primitive_root, Poly, symbols, resultant, cyclotomic_poly, factorint, totient

X = symbols('X')

# ---------- char-0 exact arithmetic in Z[zeta_n]/(zeta^{n/2}+1), n=2^mu ----------

def vec_e2_char0(A, n):
    """e_2(S) = sum_{i<j in A} zeta^{i+j}, reduced mod (zeta^{n/2}+1) -> length-h int vec."""
    h = n // 2
    v = [0] * h
    L = list(A)
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            e = (L[a] + L[b]) % n
            if e < h:
                v[e] += 1
            else:
                v[e - h] -= 1
    return tuple(v)

def vec_to_poly(v):
    return Poly(sum(c * X**i for i, c in enumerate(v)), X)

def field_norm(v, n):
    Phi = Poly(cyclotomic_poly(n, X), X)
    a = vec_to_poly(v)
    return int(resultant(Phi, a))

# ---------- Q1+Q2+Q4: the full carrier-norm spectrum ----------

def norm_spectrum(n, w, verbose=True):
    """Enumerate all w-subsets, collect distinct nonzero alpha=e_2(S) vectors, their norms."""
    seeds = {}   # alpha-vec -> multiplicity (number of w-sets producing it)
    for A in itertools.combinations(range(n), w):
        v = vec_e2_char0(A, n)
        if any(v):
            seeds[v] = seeds.get(v, 0) + 1
    norms = {}
    for v, cnt in seeds.items():
        N = field_norm(list(v), n)
        norms[v] = (N, cnt)
    nzn = [abs(N) for (N, c) in norms.values() if N != 0]
    ph = totient(n)
    C = comb(w, 2)                # # of root-of-unity terms in e_2(S)
    ceil = C ** ph               # archimedean ceiling (2r)^phi with 2r = C(w,2)
    if verbose:
        print(f"\n=== norm spectrum  n={n} w={w}  (phi(n)={ph}, e_2 has C(w,2)={C} terms) ===")
        print(f"  #distinct nonzero alpha=e_2 seeds : {sum(1 for (N,c) in norms.values() if N!=0)}")
        print(f"  #zero-norm seeds (alpha=0 over C)  : {sum(1 for (N,c) in norms.values() if N==0)}")
        if nzn:
            mx = max(nzn); mn = min(nzn)
            print(f"  |N| range  : [{mn}, {mx}]   log2(max)={log2(mx):.2f}")
            print(f"  archimedean ceiling C(w,2)^phi(n) = {C}^{ph} = {ceil}  log2={log2(ceil):.2f}")
            print(f"  ratio  log2(max|N|)/log2(ceiling) = {log2(mx)/log2(ceil):.3f}   "
                  f"(1.0 = saturates ceiling, <1 = structurally smaller)")
    return norms

def carrier_primes(n, w, qmax=None):
    """All primes q = 1 mod n dividing some nonzero N(e_2(S)). Returns dict q -> total carrier sets."""
    norms = norm_spectrum(n, w, verbose=False)
    prime_to_total = {}
    all_prime_divisors = set()
    for v, (N, cnt) in norms.items():
        if N == 0:
            continue
        for q in factorint(abs(N)):
            all_prime_divisors.add(q)
            if q % n == 1 and q > 2:
                prime_to_total[q] = prime_to_total.get(q, 0) + cnt
    return prime_to_total, all_prime_divisors

# ---------- Q2: density of carrier primes among all primes = 1 mod n ----------

def carrier_density(n, w, scan_to):
    cp, _ = carrier_primes(n, w)
    cp_set = set(cp.keys())
    # all primes 1 mod n up to scan_to
    allp = []
    m = 1
    while True:
        q = n * m + 1
        if q > scan_to:
            break
        if isprime(q):
            allp.append(q)
        m += 1
    carriers_in_range = [q for q in allp if q in cp_set]
    clean_in_range = [q for q in allp if q not in cp_set]
    print(f"\n=== carrier-prime DENSITY  n={n} w={w}  (primes q=1 mod n, q<={scan_to}) ===")
    print(f"  total primes 1 mod n in range : {len(allp)}")
    print(f"  carrier primes (q|some N)     : {len(carriers_in_range)}  "
          f"({100*len(carriers_in_range)/max(1,len(allp)):.1f}%)")
    print(f"  clean primes (defect 0)       : {len(clean_in_range)}")
    print(f"  largest carrier prime in range: {max(carriers_in_range) if carriers_in_range else None}")
    # is the carrier-prime SET bounded? once q exceeds max|N|, no NEW carriers possible.
    norms = norm_spectrum(n, w, verbose=False)
    mx = max((abs(N) for (N, c) in norms.values() if N != 0), default=0)
    print(f"  max |N| = {mx}  => NO prime q > {mx} can be a carrier (norm too small).")
    print(f"     => the carrier-prime set is FINITE, contained in divisors of the finite norm set.")
    return carriers_in_range, clean_in_range, mx

# ---------- Q3: worst-case-over-q amplification at the adversarial prime ----------

def zeta_modq(q, n):
    g = primitive_root(q)
    return pow(g, (q - 1) // n, q)

def eval_modq(v, z, q):
    acc = 0; zp = 1
    for vi in v:
        if vi:
            acc = (acc + vi * zp) % q
        zp = (zp * z) % q
    return acc % q

def adversarial_amplification(n, w):
    """For each carrier prime q, count distinct NEW e_1 (the RISE), find the worst q."""
    print(f"\n=== worst-case-over-q amplification  n={n} w={w} ===")
    # char-0 count for context
    # (the RISE count = #distinct new e_1 from halo carriers at q)
    h = n // 2
    cp, _ = carrier_primes(n, w)
    if not cp:
        print("  no carrier primes (char-0-supported w with no halo); skip.")
        return
    best = []
    for q in sorted(cp.keys()):
        z = zeta_modq(q, n)
        newe1 = set()
        halo_sets = 0
        for A in itertools.combinations(range(n), w):
            v = vec_e2_char0(A, n)
            if not any(v):
                continue  # alpha=0 over C: not a halo "new" carrier (already e_2=0 in char0)
            if eval_modq(v, z, q) == 0:
                halo_sets += 1
                e1 = eval_modq(list(_e1_vec(A, n)), z, q)
                if e1 != 0:
                    newe1.add(e1)
        best.append((q, halo_sets, len(newe1)))
    best.sort(key=lambda t: -t[2])
    print(f"  {'q':>8} {'#halo-sets':>11} {'#new-distinct-e1':>17}")
    for q, hs, ne in best[:10]:
        print(f"  {q:>8} {hs:>11} {ne:>17}")
    worst_q, worst_hs, worst_ne = best[0]
    print(f"  WORST q = {worst_q}: {worst_ne} new distinct e_1 (the adversarial RISE).")
    return best

def _e1_vec(A, n):
    h = n // 2
    v = [0] * h
    for a in A:
        a %= n
        if a < h: v[a] += 1
        else: v[a - h] -= 1
    return tuple(v)

# ---------- Q4: norm growth with n (does it reach prize scale?) ----------

def norm_growth():
    print("\n=== Q4: growth of max |N(e_2(S))| with n (toward prize scale q~n*2^128) ===")
    print(f"  {'n':>4} {'w':>3} {'phi':>5} {'maxlog2|N|':>11} {'ceil_log2':>10} {'ratio':>7} {'log2/phi':>9}")
    rows = []
    for (n, w) in [(8,3),(8,4),(16,4),(16,5),(16,6),(32,4),(32,5),(32,6)]:
        norms = norm_spectrum(n, w, verbose=False)
        nzn = [abs(N) for (N, c) in norms.values() if N != 0]
        if not nzn:
            continue
        mx = max(nzn); ph = int(totient(n)); C = comb(w, 2); ceil = C ** ph
        lm = log2(mx); lc = log2(ceil)
        rows.append((n, w, ph, lm))
        print(f"  {n:>4} {w:>3} {ph:>5} {lm:>11.2f} {lc:>10.2f} {lm/lc:>7.3f} {lm/ph:>9.3f}")
    print("\n  Interpretation: log2(max|N|)/phi(n) = per-embedding bits.  For max|N| to reach")
    print("  prize scale q~n*2^128 (~158 bits at n=2^32) you need this *times phi(n)=2^31* >= 158,")
    print("  i.e. per-embedding bits >= 158/2^31 ~ 7.4e-8 — TRIVIALLY met: the LARGEST norm vastly")
    print("  exceeds prize size at large n. The question is the SMALLEST defect-carrying norm.")

if __name__ == "__main__":
    print("wf407 / T400-05-defect : carrier-norm SPECTRUM (the verdict-driving residual)")
    print("="*72)

    # Q1: full spectrum at small enumerable scale
    norm_spectrum(16, 6)     # char-0 count 0, pure halo
    norm_spectrum(16, 4)     # char-0 supported
    norm_spectrum(32, 4)

    # Q2: carrier-prime density + FINITENESS argument
    carrier_density(16, 6, scan_to=2000)
    carrier_density(16, 4, scan_to=2000)

    # Q3: adversarial amplification
    adversarial_amplification(16, 6)

    # Q4: norm growth toward prize scale
    norm_growth()
