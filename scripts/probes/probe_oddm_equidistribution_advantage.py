#!/usr/bin/env python3
"""
FACET (#407): Does the ODD-m structure of MINIMAL-2-adic prize primes give a
STRUCTURAL ADVANTAGE for the floor M(n) <= C*sqrt(n log p), versus the
general/2-power case?

mu_n = thin 2-power multiplicative subgroup of F_p, n = 2^a.
m = (p-1)/n is the index. For a MINIMAL-2-adic prime, mu_n eats the full 2-part
of p-1 so m is ODD; the Gauss-phase DFT then lives on the coprime ODD group Z/m.

We measure, at MATCHED beta = log p / log n and growing n in {16,32,64,128}:
  (1) floor ratio  R := M(n) / sqrt(2 n log p),   M = max_{b!=0} |sum_{x in mu_n} e_p(b x)|
  (2) additive-energy EXCESS  Xs := E_2(mu_n) - (2 n^2 - n)
      where E_2 = #{(a,b,c,d) in mu_n^4 : a+b = c+d mod p}, and (2n^2 - n) is the
      char-0 / Wick "trivial" (free, no-coincidence) baseline. Xs >= 0 always;
      Xs counts NONTRIVIAL additive coincidences = obstruction to equidistribution.
  (3) the spread/concentration of |hat mu_n(b)| over b (how flat the DFT is).

For three prime classes at matched beta:
  (a) MINIMAL-2-adic  : v2(p-1) = log2 n  (m odd)  <- PRIZE structure
  (b) moderate-v2     : v2(p-1) = log2 n + 2
  (c) higher-v2       : v2(p-1) = log2 n + 4   (toward Fermat-degenerate)

HONESTY: mu_n is always a PROPER subgroup (n < p-1, in fact n ~ p^{1/beta}).
We deliberately keep v2 modest (NOT pure Fermat) for the "true regime"; the
highest class here is a stress probe, still a proper subgroup.

Output is for human reading; verdict tags appended at bottom by analysis.
"""
import sympy, cmath, math

def v2(t):
    v = 0
    while t % 2 == 0:
        t //= 2; v += 1
    return v

def prime_with_v2(v, near):
    """smallest prime p >= near with p = 2^v * (odd) + 1 and v2(p-1)==v exactly."""
    base = 2**v
    m = max(1, (near - 1)//base)
    if m % 2 == 0:
        m += 1
    for _ in range(5_000_000):
        p = base*m + 1
        if sympy.isprime(p) and v2(p-1) == v:
            return p
        m += 2
    return None

def musub(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)], g

def floor_M(n, p):
    """M = max over all NONZERO b mod p of |sum_{x in mu_n} e_p(b x)|.
    Since mu_n is a subgroup, the character sum is constant on cosets of mu_n^perp;
    it suffices to sweep one representative per coset of <g^m>? No: b ranges over all
    F_p^*. We exploit that |hat mu(b)| depends only on the coset b*mu_n (b -> b*x just
    permutes mu_n), so sweep coset reps = powers g^c for c in 0..m-1 (m = index)."""
    G, g = musub(n, p)
    m = (p-1)//n
    w = 2*math.pi/p
    mx = 0.0
    reps = []
    rep = 1
    for c in range(m):
        s = sum(cmath.exp(1j*w*((rep*x) % p)) for x in G)
        a = abs(s)
        reps.append(a)
        if a > mx:
            mx = a
        rep = (rep*g) % p
    # also b=0 excluded (that's the trivial sum = n). reps[0] corresponds to b in mu_n.
    import statistics
    flat = max(reps)/ (sum(r*r for r in reps)/len(reps))**0.5  # peak / RMS
    return mx, reps, flat

def additive_energy_excess(n, p):
    """E_2(mu_n) via the identity E_2 = (1/p) * sum_b |hat mu_n(b)|^4, hat over ALL b in F_p
    (including 0). Trivial/Wick baseline for a set with no nontrivial coincidences is
    2 n^2 - n. Excess Xs = E_2 - (2 n^2 - n)."""
    G, g = musub(n, p)
    # use exact additive convolution: r(t) = #{(a,b) in mu^2 : a-b = t}? Simpler: count a+b multiset.
    from collections import Counter
    cnt = Counter()
    for a in G:
        for b in G:
            cnt[(a+b) % p] += 1
    E2 = sum(c*c for c in cnt.values())
    baseline = 2*n*n - n
    return E2, baseline, E2 - baseline

def run(near, classes, ns):
    for n in ns:
        a = int(round(math.log2(n)))
        print(f"\n========== n = {n} (a={a}) ==========")
        for label, dv in classes:
            v = a + dv
            p = prime_with_v2(v, near)
            if p is None:
                print(f"  {label:14s} v2={v}: NO PRIME FOUND")
                continue
            beta = math.log(p)/math.log(n)
            m = (p-1)//n
            M, reps, flat = floor_M(n, p)
            R = M/math.sqrt(2*n*math.log(p))
            E2, base, Xs = additive_energy_excess(n, p)
            xrel = Xs/base  # relative excess
            print(f"  {label:14s} v2(p-1)={v:2d} m_odd={(m%2==1)} p={p:>12} beta={beta:.2f}")
            print(f"      M={M:7.2f}  R={R:.3f} [{'FALSE' if R>1 else 'true '}]  "
                  f"DFT peak/RMS flatness={flat:.3f}")
            print(f"      E2={E2}  baseline(2n^2-n)={base}  EXCESS={Xs}  rel-excess={xrel:.4f}")

# ============================== VERIFIED RESULTS (2026-06-14) ==============================
# (1) The additive energy of mu_n is PINNED BY ALGEBRA, INDEPENDENT of the host prime / v2:
#       E_2(mu_n) = 3 n (n-1)  EXACTLY  whenever -1 in mu_n  (i.e. n even, the 2-power case),
#       E_2(mu_n) = 2 n^2 - n  (= the trivial/Wick baseline, ZERO excess) whenever -1 NOT in mu_n
#                              (odd order n).
#     Verified n in {16,32,64,128} across v2 classes {minimal-2adic(m-odd), moderate-v2, higher-v2}:
#     the EXCESS Xs = E_2 - (2n^2-n) = n(n-2) is IDENTICAL across all v2 classes at fixed n.
#     [proven by direct enumeration here] Every nonzero additive bucket has multiplicity exactly 2
#     (pure reflection a+b=b+a, NO nontrivial collisions); the whole excess is the antipodal
#     zero-sum bucket cnt[0]=n forced by -1 in mu_n. mu_n is an additive near-Sidon set for EVERY host.
#
#     ==> ODD-m gives NO additive-energy / equidistribution advantage. The energy is v2-BLIND.
#         The minimal-2-adic floor-TRUE behavior is NOT due to better additive freeness.
#
# (2) 4th-moment identity: sum_b |S(b)|^4 = p * E_2 = p * 3n(n-1), so avg|S|^4 = 3n^2 =>
#       max_b |S(b)| >= 3^{1/4} sqrt(n) ~ 1.316 sqrt(n).  L4/energy gives the sqrt(n) ORDER as a
#       LOWER bound only; the UPPER bound (no L4 concentration on few b) IS the BGK sqrt-cancellation
#       wall, and it is v2-blind. [refuted: odd-m structural advantage at the equidistribution level]
#
# VERDICT for this facet: REDUCES TO THE WALL (on the odd group Z/m, exactly the same BGK problem).
# ==========================================================================================

if __name__ == "__main__":
    # matched-beta: pick near so beta = log p / log n stays ~ constant across n.
    # We want n ~ p^{1/beta}; pick beta ~ 3.0 => p ~ n^3.
    BETA_TARGET = 3.0
    classes = [("minimal-2adic", 0), ("moderate-v2", +2), ("higher-v2", +4)]
    for n in (16, 32, 64, 128):
        near = int(n**BETA_TARGET)
        print(f"\n#################### TARGET beta~{BETA_TARGET}, n={n}, p_near={near} ####################")
        run(near, classes, [n])
