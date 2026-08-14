#!/usr/bin/env python3
"""
probe_407_census_core_equivalence.py  (#407 / #371 census-vs-CORE lane)

LANE (brief lane 4, uncontested): the count/census face (CensusDomination) whose EQUIVALENCE
to CORE is ASSERTED ("the $1M obligation in census normal form") but NEVER proven. Proving /
mapping that equivalence is itself a real brick.

THE IN-TREE ARCHITECTURE (CensusDominationWeld.lean + UniversalAlignmentLaw + KKH26AlignmentSupply):
  (U) UPPER HALF  (badScalars_card_le_alignable, PROVEN):  #bad-scalars(band a) <= #alignable-a-sets.
  (S) SUPPLY HALF (KKH26AlignmentSupply, PROVEN lower bd): the KKH26 line realizes #alignable >= fibre count.
  (W) WELD        (CensusDomination => delta*-pin, PROVEN): granting  #alignable <= K (all pairs, deep bands),
                                                            delta* = 1 - r/2^mu, with K/p <= eps*.
  => CensusDomination is the load-bearing HYPOTHESIS. The claim "it IS the prize" needs the equivalence
     CensusDomination <=> CORE.  Only (U) is proven; the REVERSE (is #alignable no bigger than CORE forces?)
     is the open content. If #alignable >> #bad at the prize regime, the census bound (U) is LOSSY =>
     CensusDomination is STRICTLY STRONGER than CORE (proving it is harder than the prize, route over-shoots).

THE EXACT OBJECTS (from UniversalAlignmentLaw / probe_alignment_census semantics — matched here):
  - domain mu_n = <g> subgroup of F_p^*, |mu_n| = n, smooth prize domain n = 2^mu, prize prime p ~ n^beta.
  - k = dimension (deg < k codewords). band a (a-set = a-subset of mu_n).
  - residual: for a (k+1)-tuple T of nodes, e_j(T) = divided difference [x_{t0..tk}] u_j  (j=0,1).
  - an a-set S is ALIGNED at gamma iff ALL its nondegenerate (k+1)-subtuples share the SAME ratio
    gamma = -e0(T)/e1(T). #alignable-a-sets = #{S : exists gamma, S gamma-aligned, with a nondegenerate tuple}.
  - a gamma is BAD iff some a-set is gamma-aligned (=> the far line x^a+gamma x^b agrees with a deg<k word
    on S). #bad(band a) = #distinct pinned ratios gamma.
  - CORE / M-driven analytic count = #bad. The census K bounds #alignable. (U): #bad <= #alignable.

THE MEASUREMENT (probe-first, exact mod-p arithmetic, PROPER subgroup, prize primes, smooth n=2^mu):
  For the FAR-LINE pair u0 = x^A, u1 = x^B (A,B the far exponents), at the binding deep band a:
    (1) #alignable-a-sets    (census K side)
    (2) #bad = #distinct pinned gamma   (CORE side)
    (3) the RATIO #alignable / #bad  -> TIGHT (~1) means census faithful to CORE; LOSSY (>>1) means
        CensusDomination strictly stronger than CORE (the route proves more than the prize).
  Compare smooth n=2^mu vs a THICK control (n composite-but-not-2-power, or full-ish) -- rule 3: the
  equivalence GAP must be thinness-sensitive if the census route is to be the right CORE encoding.

HONESTY: this measures the (U)-inequality SLACK. A tight ratio supports the asserted equivalence (does
NOT prove it -- the analytic <=> combinatorial identity still needs a proof). A lossy ratio is a
refutation-grade finding: CensusDomination != CORE (strictly stronger), so the census normal form is
NOT the prize but an over-strong sufficient condition. Either way the equivalence claim gets MAPPED.
No Lean changes -> axiom-clean trivially. NEVER n=q-1.
"""
import itertools, sys
from collections import defaultdict

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def prize_prime(n, beta=4.0):
    p = int(n**beta)
    p += (1 - p) % n  # make p == 1 mod n  (so mu_n exists)
    while not (isprime(p) and (p-1) % n == 0):
        p += n
    return p

def find_g(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in [2] if n % 2 == 0):
            # verify exact order n
            if all(pow(x, d, p) != 1 for d in range(1, n) if n % d == 0 and d < n):
                return x
    raise ValueError("no generator")

def divided_diff(idxs, uvals, xs, p):
    """[x_{idxs}] u  = sum_i u_i / prod_{j!=i}(x_i - x_j)  mod p."""
    total = 0
    for i in idxs:
        den = 1
        for j in idxs:
            if i == j: continue
            den = (den * ((xs[i] - xs[j]) % p)) % p
        total = (total + uvals[i] * pow(den, p-2, p)) % p
    return total

def census_and_bad(n, p, g, A, B, k, a, max_sets=None):
    """
    Returns (#alignable a-sets, #distinct pinned gammas, sample) for far-line u0=x^A,u1=x^B.
    a-set S (a-subset of the n nodes) is alignable iff all its nondeg (k+1)-subtuples share one
    ratio gamma=-e0/e1; that gamma is 'bad'. Exact mod-p. EXPENSIVE: C(n,a) * C(a,k+1).
    """
    xs = [pow(g, i, p) for i in range(n)]
    u0 = [pow(xx, A, p) for xx in xs]
    u1 = [pow(xx, B, p) for xx in xs]
    alignable = 0
    bad_gammas = set()
    nodes = list(range(n))
    cnt = 0
    for S in itertools.combinations(nodes, a):
        cnt += 1
        if max_sets and cnt > max_sets:
            break
        gamma = None
        ok = True
        has_nondeg = False
        for T in itertools.combinations(S, k+1):
            e0 = divided_diff(T, u0, xs, p)
            e1 = divided_diff(T, u1, xs, p)
            if e1 == 0:
                if e0 != 0:
                    ok = False; break      # degenerate-incompatible: cannot align
                continue                    # both zero: this tuple is degenerate, skip
            has_nondeg = True
            gT = (-e0 * pow(e1, p-2, p)) % p
            if gamma is None:
                gamma = gT
            elif gamma != gT:
                ok = False; break
        if ok and has_nondeg and gamma is not None:
            alignable += 1
            bad_gammas.add(gamma)
    return alignable, len(bad_gammas), cnt

def main():
    print("# census-vs-CORE equivalence: is #alignable (census K) ~ #bad (CORE), or LOSSY? (#407/#371)")
    print("# (U) proven: #bad <= #alignable. Equivalence to CORE needs the REVERSE to be tight.\n")
    hdr = f"{'n':>4} {'mu':>3} {'p':>10} {'beta':>5} {'k':>3} {'a':>3} {'#align':>8} {'#bad':>6} {'ratio':>7} {'verdict':>16}"
    print(hdr); print("-"*len(hdr))
    # smooth prize domain, small-but-real: n=8 (mu=3), n=16 (mu=4). k = dimension; far band a near boundary.
    configs = [
        (8, 2, 3.0), (8, 2, 4.0),
        (16, 4, 3.0), (16, 4, 4.0),
        (16, 2, 4.0),
    ]
    for n, k, beta in configs:
        mu = n.bit_length()-1
        p = prize_prime(n, beta)
        try:
            g = find_g(p, n)
        except ValueError:
            print(f"{n:>4} {mu:>3} {p:>10} {beta:>5.1f}  (no gen)"); continue
        # far line exponents A,B in [k, n): choose the canonical far pair A=k, B=k+1 (adjacent far line),
        # matching the deltaStarReduction far-line object (x^a + gamma x^b, a,b >= k).
        A, B = k, k+1
        # binding band: deep band a around (1-delta)n; sweep a = k+1 .. n//2 small range
        for a in range(k+1, min(n//2+2, n)):
            align, bad, cnt = census_and_bad(n, p, g, A, B, k, a)
            if align == 0:
                continue
            ratio = align / bad if bad else float('inf')
            verdict = "TIGHT(faithful)" if ratio <= 1.5 else ("mild-loss" if ratio <= 4 else "LOSSY(stronger)")
            print(f"{n:>4} {mu:>3} {p:>10} {beta:>5.1f} {k:>3} {a:>3} {align:>8} {bad:>6} {ratio:>7.2f} {verdict:>16}")
    print("\n# READ: ratio = #alignable / #bad. ~1 => census faithful to CORE (supports asserted equivalence).")
    print("#       >>1 => CensusDomination STRICTLY STRONGER than CORE (route over-shoots; proving it is")
    print("#              harder than the prize). The equivalence claim is then FALSE as stated.")

if __name__ == '__main__':
    main()
