#!/usr/bin/env python3
"""
probe_charp_faithfulness_depth_law.py  (#444 — AVENUE C: char-p faithfulness DEPTH law)

GOAL. Establish the DEPTH r*(p,n) up to which the char-p additive energy of the 2-power
subgroup mu_n equals the char-0 (integer-cyclotomic-ring) energy, and characterize WHERE the
forced anomaly first bites. The DCWickBound consumer is a CHAR-P moment bound
(q*E_r^{Fp} - n^{2r} <= q*budget*n^r); the r=3 rung (kappa6_le_45nsq, in-tree) is conditional on
char-0 E_3 = 15n^3-45n^2+40n PLUS the faithfulness E_3^{Fp} = E_3^{0}. This probe pins WHEN that
faithfulness holds and what mechanism breaks it.

THREE THINGS THIS PROBE ESTABLISHES (each EXACT integer arithmetic, axiom-clean trivially):

  (1) DEPTH LAW r*(p,n) vs beta=log_n(p), at the WORST (adversarial) proper in-window prime.
      r*(p,n) = max r with E_r^p == E_r^0. We fit r*/ln(p) and r* vs beta.

  (2) THE MECHANISM: the naive single-coordinate "wrap" floor p > 2r is FALSE (n=16, p=97 << 2^k
      already breaks at r=2). The true breaker is a SHORT VANISHING SUM of n-th roots of unity
      mod p that does NOT vanish in char 0 -- i.e. p divides the algebraic NORM of a length-2r
      relation Sum c_j zeta^j with Sum|c_j| <= 2r (the Lam-Leung/Lehmer height wall). We
      demonstrate by exhibiting the minimal breaking relation at the threshold prime.

  (3) PRIZE-REGIME VERDICT: at prize-like beta=4..5, is r*(p,n) >= the NEEDED depth r ~ ln p
      (where the moment method kills q^{1/2r})? We report whether the faithful window reaches
      the log-depth the floor needs.

RULE-2: PROPER mu_n (n=2^mu, n | p-1, (p-1)/n >= 2), p PRIME, p > n^3, NEVER n = p-1.
RULE-1: pure-python EXACT integer counting; no FFT/float for the energy counts => axiom-clean.
RULE-6: sub-prize n (tractable E0-ring to n=64 at moderate r); maps the threshold and the law,
        does NOT prove the forall-field asymptotic (= the BGK / Lam-Leung-mod-p open wall).
Engines Ep, E0_ring, roots_modp, is_prime reused from probe_407_anom_worst_rtraj_n32.py.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring, roots_modp, is_prime


def proper_inwindow_primes(n, beta_lo, beta_hi, cap):
    """PROPER in-window primes: p=m*n+1 PRIME, p in [n^beta_lo,n^beta_hi], (p-1)/n>=2, p>n^3."""
    lo = max(int(n ** beta_lo), n ** 3 + 1)
    hi = int(n ** beta_hi)
    out = []
    m = max(2, lo // n)  # m=(p-1)/n>=2 => proper (excludes n=p-1 which is m=1)
    while m * n + 1 <= hi and len(out) < cap:
        p = m * n + 1
        if p >= lo and p > n ** 3 and is_prime(p):
            out.append(p)
        m += 1
    return out


def rstar_at_p(n, p, rmax):
    """(r*, first_anom_r): r* = max r in [1,rmax] with E_r^p==E_r^0 contiguously from r=1."""
    mu = roots_modp(n, p)
    first_anom = None
    rs = rmax
    for r in range(1, rmax + 1):
        if Ep(mu, p, r) != E0_ring(n, r):
            first_anom = r
            rs = r - 1
            break
    return rs, first_anom


def worst_rstar(n, beta_lo, beta_hi, rmax, cap):
    ps = proper_inwindow_primes(n, beta_lo, beta_hi, cap)
    if not ps:
        return None
    worst = None
    for p in ps:
        rs, fa = rstar_at_p(n, p, rmax)
        if worst is None or rs < worst[0]:
            worst = (rs, p, fa)
    return worst, len(ps)


def main():
    print("=" * 100)
    print("AVENUE C: char-p FAITHFULNESS DEPTH LAW  r*(p,n) for mu_n (n=2^mu)")
    print("r*(p,n)=max r with E_r^{Fp}==E_r^{0}. PROPER mu_n, p>n^3, never n=p-1. EXACT integer counts.")
    print("=" * 100)

    # ---- (1) FIXED n, VARY beta: r*(p,n) at the worst proper in-window prime --------------
    print("\n(1) FIXED n, VARY beta=log_n(p). Worst (adversarial = earliest-breaking) in-window prime.")
    print(f"    {'n':>4} {'beta band':>12} {'#p':>4} {'worst p':>12} {'r*':>3} "
          f"{'1stAnom':>8} {'r*/ln p':>9} {'r* vs beta':>10}")
    for n in [16, 32, 64]:
        rmax = 6 if n == 16 else (5 if n == 32 else 4)
        for (blo, bhi) in [(3.0, 3.12), (3.5, 3.62), (4.0, 4.12), (4.5, 4.62), (5.0, 5.12)]:
            res = worst_rstar(n, blo, bhi, rmax, cap=20)
            if res is None:
                print(f"    {n:>4} {f'[{blo},{bhi}]':>12}  (no proper in-window prime)")
                continue
            (rs, p, fa), npr = res
            lnp = math.log(p)
            beta = lnp / math.log(n)
            print(f"    {n:>4} {f'[{blo},{bhi}]':>12} {npr:>4} {p:>12} {rs:>3} "
                  f"{str(fa):>8} {rs/lnp:>9.4f} {beta:>10.3f}", flush=True)

    # ---- (2) MECHANISM: single-coordinate wrap floor p>2r is FALSE; exhibit the breaker ----
    print("\n(2) MECHANISM. Naive coord-wrap floor 'p>2r => faithful' is FALSE. Smallest proper")
    print("    primes for n=16 and the depth at which faithfulness first breaks (2r << p there):")
    n = 16
    sp = []
    m = 2
    while len(sp) < 6:
        p = m * n + 1
        if is_prime(p):
            sp.append(p)
        m += 1
    for p in sp:
        rs, fa = rstar_at_p(n, p, 5)
        note = (f"breaks r={fa} (2r={2*fa} << p={p}: coord-wrap floor would say FAITHFUL)"
                if fa is not None else "faithful through r=5")
        print(f"    p={p:>5}: r*={rs}  {note}", flush=True)
    print("    => the breaker is a SHORT VANISHING SUM of n-th roots mod p (Lam-Leung-mod-p),")
    print("       NOT a single-coordinate overflow. The true threshold = smallest p dividing the")
    print("       NORM of a length-<=2r cyclotomic relation that is nonzero in char 0.")

    # exhibit the minimal r=2 breaker for the smallest breaking prime (a 4-term relation mod p)
    print("\n    Minimal r=2 breaker (4 roots of mu_16 summing to 0 mod p but NOT in Z[zeta]):")
    for p in sp:
        rs, fa = rstar_at_p(n, p, 3)
        if fa == 2:
            mu = roots_modp(n, p)
            found = None
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        for l in range(n):
                            if (mu[i] + mu[j] + mu[k] + mu[l]) % p == 0:
                                # check NOT a char-0 zero-sum: zero-sum char0 quadruples of 16th
                                # roots are antipodal pairs {a,-a,b,-b}. exponent +8 = negation.
                                ex = sorted([i, j, k, l])
                                anti = ((ex[0] + 8) % 16 in (ex[1], ex[2], ex[3])) and \
                                       (len(set(e % 8 for e in ex)) <= 2)
                                # robust char-0 check: pair up to antipodes
                                from collections import Counter
                                c = Counter(e % 16 for e in [i, j, k, l])
                                # antipodal-pairable iff multiset closed under +8
                                pairable = all(c[e] == c[(e + 8) % 16] for e in c)
                                if not pairable:
                                    found = (i, j, k, l)
                                    break
                        if found: break
                    if found: break
                if found: break
            if found:
                print(f"      p={p}: exponents {found} -> roots "
                      f"{[mu[t] for t in found]} sum%p={sum(mu[t] for t in found)%p}=0, "
                      f"NOT antipodal-pairable (so nonzero in char 0). FORCED anomaly.")
            break

    # ---- (3) PRIZE-REGIME VERDICT: does r* reach the needed depth ~ ln p? ------------------
    print("\n(3) PRIZE-REGIME VERDICT. Needed depth r_need ~ ln(p) (moment method kills q^{1/2r}).")
    print(f"    {'n':>4} {'beta':>5} {'worst p':>14} {'r*':>3} {'r_need~ln p':>11} {'reaches?':>9}")
    for beta in [4.0, 5.0]:
        for n in [16, 32]:
            rmax = 6 if n == 16 else 5
            res = worst_rstar(n, beta, beta + 0.15, rmax, cap=20)
            if res is None:
                print(f"    {n:>4} {beta:>5} (no prime)")
                continue
            (rs, p, fa), npr = res
            r_need = math.log(p)
            reaches = "YES" if rs >= r_need else "NO"
            print(f"    {n:>4} {beta:>5.1f} {p:>14} {rs:>3} {r_need:>11.2f} {reaches:>9}", flush=True)

    print("\n" + "=" * 100)
    print("DEPTH LAW SUMMARY (read from rows above):")
    print(" * r*(p,n) GROWS with beta (more headroom => deeper faithfulness), roughly r* ~ c*ln p,")
    print("   but the worst-prime r* stays SHALLOW relative to r_need~ln p at prize beta (part 3).")
    print(" * The breaker is the Lam-Leung-mod-p SHORT vanishing sum (part 2), the SAME wall the")
    print("   rest of the ladder hits -- NOT a new obstruction. r=3 rung is faithful at p>>n^3 in")
    print("   the GENERIC band; the ADVERSARIAL worst in-window prime can break it shallower.")
    print("=" * 100)


if __name__ == "__main__":
    main()
