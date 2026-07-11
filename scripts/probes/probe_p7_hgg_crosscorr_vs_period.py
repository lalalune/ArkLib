#!/usr/bin/env python3
"""
P7-HGG-cross-correlation angle (issue #407 / Proximity Prize).

QUESTION: Does the Helleseth-Golomb-Gong (HGG) cross-correlation theory deliver
the Ramanujan-scale sup-norm bound M(mu_n) <= sqrt(n log m) for the PRIZE object
(incomplete Gauss sum over a thin 2-power multiplicative subgroup mu_n of F_p^x),
or does it only address a STRUCTURALLY DIFFERENT object (complete trace sums over
the FULL field F_{p^n}^x)?

WHAT HGG ACTUALLY BOUNDS (verified from arXiv:2407.16072 "An updated review on
crosscorrelation of m-sequences", Helleseth & Gong / Golomb-Gong lineage):

  C_d(tau) = sum_{t=0}^{p^n - 2} omega^{ Tr(alpha^{t+tau}) - Tr(alpha^{d t}) }
           = sum_{x in F_{p^n}^x} omega^{ Tr(c*x) - Tr(x^d) }     (c = alpha^tau)

  where omega = e^{2 pi i / p}, Tr : F_{p^n} -> F_p the absolute trace,
  d coprime to N = p^n - 1, sum runs over the FULL multiplicative group.

  Magnitude (Gold/Kasami-Welch, n=2m, p=2): values  -1, -1 +- 2^{m+1}.
    => C_max ~ 2^{m+1} = 2*sqrt(2^{2m}) ~ 2*sqrt(N).   [Sidelnikov/Welch sqrt(N)]
  General odd p (Trachtenberg-Helleseth, Thm 3): values -1, -1 +- p^{(n+e)/2}.
    => C_max ~ p^{(n+e)/2} ~ sqrt(N) * p^{e/2},  e = gcd(n,k).

So HGG delivers a GENUINE O(sqrt(N)) (square-root cancellation) bound -- but for
a COMPLETE sum over F_{p^n}^x of period N = p^n - 1, NOT for the prize's
INCOMPLETE sum over a thin subgroup mu_n of F_p^x.

THIS PROBE tests the structural correspondence three ways:

 (A) FIELD MISMATCH. The prize sum lives in F_p (prime field), sums over a
     subgroup mu_n of index m = (p-1)/n. HGG lives in F_{p^n} (extension),
     sums over the WHOLE F_{p^n}^x. Identify what would have to be true to map
     one to the other, and show it forces n = p^n - 1 (i.e. mu_n = whole group),
     which is the COMPLETE-sum regime where sqrt(N) is just Weil, useless for
     the prize (n < sqrt(p)).

 (B) COMPLETE-vs-INCOMPLETE. Realize eta_b = sum_{x in mu_n} e_p(b x) as a
     RESTRICTED sum and show the HGG/Weil sqrt cancellation, when "completed"
     to run over all of F_p^x (the only regime HGG-style trace identities cover),
     loses the subgroup gain: completion bound is sqrt(p) >> n for n < sqrt(p),
     i.e. VACUOUS in the prize regime n ~ p^{1/4}.

 (C) NUMERICAL: directly compute (i) prize sup-norm M(mu_n) over F_p, and
     (ii) the best HGG-style "complete trace sum" surrogate, and show the
     latter does NOT bound the former at Ramanujan scale -- the only thing
     sqrt(N) controls is the FULL sum, whose magnitude is p^{n/2}, astronomically
     larger than the prize target sqrt(n log m).
"""

import cmath, math
from math import gcd, log, sqrt, pi

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def eta_b(b, mu_n, p):
    """Incomplete Gauss sum (prize period) sum_{x in mu_n} e_p(b x)."""
    s = 0j
    for x in mu_n:
        s += cmath.exp(2j*pi*(b*x % p)/p)
    return s

def subgroup_2power(p, mu):
    """Order-n=2^mu multiplicative subgroup of F_p^x (requires n | p-1)."""
    n = 1 << mu
    assert (p-1) % n == 0, f"n={n} does not divide p-1={p-1}"
    # find generator g of F_p^x then take g^{(p-1)/n}
    # small p: brute-force a generator
    def order(a):
        o, t = 1, a % p
        while t != 1:
            t = (t*a) % p; o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p-1:
            g = cand; break
    h = pow(g, (p-1)//n, p)
    H = set()
    t = 1
    for _ in range(n):
        H.add(t); t = (t*h) % p
    assert len(H) == n
    return sorted(H)

def prize_supnorm(p, mu):
    n = 1 << mu
    H = subgroup_2power(p, mu)
    M = max(abs(eta_b(b, H, p)) for b in range(1, p))
    return n, M

def main():
    print("="*78)
    print("P7-HGG: cross-correlation theory vs the prize incomplete Gauss sum")
    print("="*78)

    # ----- Part (C): the prize object, generic & structured primes -----
    print("\n[C] PRIZE OBJECT  M(mu_n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)|")
    print("    compared with  HGG/Weil COMPLETE-sum scale sqrt(p)  and the")
    print("    Ramanujan target sqrt(2 n log m),  m = (p-1)/n.")
    print(f"{'p':>9} {'type':>10} {'n':>6} {'m':>9} {'M':>9} "
          f"{'sqrt(2n*lnm)':>12} {'sqrtp(HGG)':>11} {'M/target':>9} {'M/sqrtp':>9}")
    # proper smooth subgroups: n=2^mu, n | p-1, p PRIME, n != p-1
    cases = [
        # (p, mu)  -- p prime, 2^mu | p-1, 2^mu < p-1 (proper)
        (97, 4),     # n=16, m=6
        (193, 5),    # n=32, m=6
        (257, 4),    # n=16, m=16  (Fermat F3 = 257, structured 2-group!)
        (769, 5),    # n=32, m=24
        (12289, 6),  # n=64, m=192 (NTT prime, smooth)
        (40961, 6),  # n=64, m=640
        (65537, 4),  # FERMAT F4, n=16, m=4096  (maximally structured)
    ]
    for p, mu in cases:
        if not is_prime(p):
            print(f"{p:>9}  NOT PRIME -- skip"); continue
        n = 1 << mu
        if (p-1) % n != 0 or n == p-1:
            print(f"{p:>9}  n=2^{mu} not a PROPER divisor of p-1 -- skip"); continue
        m = (p-1)//n
        _, M = prize_supnorm(p, mu)
        target = sqrt(2*n*log(m)) if m > 1 else float('nan')
        sqrtp = sqrt(p)
        ptype = "FERMAT" if (p in (257, 65537)) else "generic"
        print(f"{p:>9} {ptype:>10} {n:>6} {m:>9} {M:>9.3f} "
              f"{target:>12.3f} {sqrtp:>11.3f} {M/target:>9.3f} {M/sqrtp:>9.3f}")

    print("""
  READING (C): the prize target sqrt(2 n log m) is the Ramanujan/BGK scale.
  The HGG/Weil 'complete-sum' scale is sqrt(p) (square-root of the FIELD size,
  not of n). In the prize regime n ~ p^{1/4}:  sqrt(p) = p^{1/2} = n^2 >> n,
  so the complete-sum sqrt-cancellation bound is WORSE THAN TRIVIAL (M <= n).
  HGG's sqrt(N) is sqrt of the period of the SEQUENCE = sqrt of the GROUP it
  sums over; for the prize that group is mu_n (size n), and the prize asks
  exactly for sqrt(n)-cancellation of an INCOMPLETE sum -- which HGG does NOT
  provide (HGG only gives sqrt of a COMPLETE sum's range).
""")

    # ----- Part (A)/(B): the structural reduction, made explicit -----
    print("[A/B] STRUCTURAL CORRESPONDENCE TEST")
    print("""
  HGG cross-correlation:   C_d(tau) = sum_{x in F_{p^n}^x} w^{Tr(c x) - Tr(x^d)}
       - sum domain  = F_{p^n}^x  (FULL group, size p^n - 1 = N)
       - phase       = Tr(c x) - Tr(x^d)  (two trace-monomials, d-decimation)
       - magnitude   = O(sqrt(N)) = O(p^{n/2})  [Sidelnikov; sharp 3-valued]

  Prize period:            eta_b   = sum_{x in mu_n} e_p(b x)
       - sum domain  = mu_n <= F_p^x  (THIN subgroup, size n, INDEX m>1)
       - phase       = e_p(b x) = e^{2 pi i b x / p}  (single linear char of F_p)
       - target      = O(sqrt(n log m)),  n ~ p^{1/4}  (incomplete; BGK-open)

  To IDENTIFY eta_b with some C_d(tau) one needs simultaneously:
    (1) the same ambient field:  F_p  vs  F_{p^n}.  Forces extension degree 1,
        i.e. n_ext = 1, so 'Tr' is identity and C_d sums over F_p^x (all p-1
        elements), NOT over mu_n.
    (2) the same SUM DOMAIN.  C_d sums over the WHOLE group; eta_b sums over a
        PROPER subgroup mu_n (index m = (p-1)/n > 1).  An HGG sum is INTRINSICALLY
        complete.  Restricting to a subgroup is exactly the 'incomplete Gauss sum'
        operation that destroys the Weil/HGG sqrt cancellation (need completion,
        which reintroduces a factor up to the full sqrt(p)).
""")

    # Quantify (B): complete-sum bound, when restricted to subgroup via completion,
    # gives sqrt(p), vacuous for n < sqrt(p).
    print("  [B] COMPLETION COST (why HGG sqrt-cancellation does not survive")
    print("      restriction to the thin subgroup):")
    print(f"{'n=2^mu':>8} {'p~n^beta':>14} {'beta':>5} {'n(trivial)':>11} "
          f"{'sqrt(p) HGG':>12} {'sqrt(n log m)':>14} {'HGG vacuous?':>13}")
    for mu, beta in [(10,4),(20,4),(30,4),(30,5),(35,4.66)]:
        n = 1 << mu
        p = n**beta            # prize scale p ~ n^beta, beta in [4,5]
        m = p / n
        hgg = sqrt(p)
        ram = sqrt(n*log(m))
        vac = "YES (>= n)" if hgg >= n else "no"
        print(f"{n:>8} {p:>14.3e} {beta:>5.2f} {n:>11.3e} "
              f"{hgg:>12.3e} {ram:>14.3e} {vac:>13}")

    print("""
  READING (B): at the prize parameter p ~ n^beta, beta in [4,5], the HGG/Weil
  complete-sum scale sqrt(p) = n^{beta/2} = n^{2..2.5} EXCEEDS the trivial bound
  n.  So 'complete' sqrt-cancellation is vacuous; the prize wants sqrt(n)-scale
  cancellation of an INCOMPLETE sum, an object HGG theory never touches.
""")

    print("="*78)
    print("VERDICT (P7-HGG): NO-GAIN / REDUCES-TO-BGK.")
    print("""HGG cross-correlation delivers genuine O(sqrt(N)) square-root cancellation,
but N is the period of a COMPLETE trace sum over the FULL field F_{p^n}^x. That
is the Weil/Sidelnikov regime: sqrt of the GROUP SUMMED OVER.  The prize object
is an INCOMPLETE sum over a thin subgroup mu_n (index m>1) of the PRIME field
F_p, and asks for sqrt(n)-cancellation where n = |mu_n| << p.  Mapping eta_b to
an HGG C_d(tau) forces (i) extension degree 1 and (ii) the sum domain to be the
WHOLE group -- i.e. mu_n = F_p^x, the complete-sum case, where sqrt-cancellation
is just sqrt(p) = n^{2..2.5}, WORSE than the trivial bound n in the prize regime.
HGG therefore gives NOTHING the per-frequency BGK statement lacks; the gap is the
incomplete-sum/thin-subgroup gap that di Benedetto (n^{0.989}) addresses and that
remains ~25yr open below n^{1/2}.  Same wall.""")
    print("="*78)

if __name__ == "__main__":
    main()
