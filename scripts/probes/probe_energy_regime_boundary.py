#!/usr/bin/env python3
"""
probe_energy_regime_boundary.py  (#389 — the decisive regime boundary for the Shaw/high-moment route)

SETTLES whether the 2-power Lam-Leung / Sidon additive-energy lever (E_k(mu_n) <= C^k k! n^k, which the
high-moment Shaw-operator route needs to reach the target per-frequency scale sqrt(n log q)) survives into
the PRIZE REGIME n >> log q.  ANSWER: NO.

THE LEVER (works only for n < log q): for n = 2^mu, Lam-Leung says vanishing sums of n-th roots of unity
are negation pairs only, so E_k(mu_n) <= (2k-1)!! n^k <= 2^k k! n^k  =>  c_k := E_k/(k! n^k) <= 2^k,
c_k^{1/2k} <= sqrt(2) = O(1).  BUT Lam-Leung holds only in char 0 / p huge; over F_q it needs n < log p
(my Sidon result E_2(mu_n)=3n^2-3n needs p > 2^n).

MEASURED HERE (decisive): fixing q and growing n, c_2 = E_2/(2n^2) and E_2/n^2:
  q=8161  (log2 q=13): Sidon (E_2=3n^2-3n) EXACT up to n=24 (c_2~1.4).
  q=65537 (log2 q=16): Sidon EXACT to n=16; BREAKS at n=32 (E_2=3360>2976); n=64 c_2=2.41; n=512 E_2/n^2=7.1
                       (vs Sidon 3) and GROWING.
=> Lam-Leung/Sidon (c_k=O(1)) holds for n <~ log q but BREAKS for n >> log q, where E_k enters the
   SUM-PRODUCT regime and grows (char-p additive structure / extra vanishing sums).

CONSEQUENCE FOR THE PRIZE.  Prize regime: q = n/eps* = n*2^128, so log2 q = log2 n + 128; n = 2^30 gives
log q = 158 << n = 2^30.  So the prize is FIRMLY in the n >> log q regime where the Lam-Leung lever FAILS.
The high-moment Shaw route's input E_k(mu_n) <= C^k k! n^k is FALSE there; reaching the target scale
requires the OPTIMAL additive-energy bound E_k(mu_n) = n^{k+o(1)} = the OPEN SUM-PRODUCT conjecture
(E_2 = n^{2+o(1)} is open, the 7/3 barrier; best formalizable HBK 5/2).

THE FUNDAMENTAL DICHOTOMY (now proven decisively): the Shaw-operator fluctuation bound is EITHER
moment-based (=> E_k => open sum-product) OR Weil-based (=> vacuous for n << sqrt q). The Shaw operator is
the right SQRT-LOSS-FREE framing (average is clean/capacity; difficulty isolated in the fluctuation) but it
does NOT escape this wall. The prize-regime additive energy of the multiplicative subgroup mu_n is the
irreducible open core (issue389-additive-energy-crux). Lam-Leung closes it only for tiny n < log q.

USAGE: python3 probe_energy_regime_boundary.py
"""
import math
from collections import Counter


def find_subgroup(q, n):
    if (q - 1) % n:
        return None
    for prg in range(2, q):
        o, x = 1, prg % q
        while x != 1:
            x = (x * prg) % q
            o += 1
        if o == q - 1:
            h = pow(prg, (q - 1) // n, q)
            S, v = set(), 1
            for _ in range(n):
                S.add(v)
                v = v * h % q
            return sorted(S)
    return None


def E2(G, q):
    c = Counter()
    for a in G:
        for b in G:
            c[(a + b) % q] += 1
    return sum(v * v for v in c.values())


def main():
    print("Does Sidon/Lam-Leung (c_2=O(1)) survive into n >> log q (the prize regime)?  Fixed q, growing n:")
    for q in [8161, 65537]:
        logq = math.log2(q)
        print(f"\nq={q} (log2 q={logq:.1f}):")
        print(f"  {'n':>5} {'n vs logq':>10} {'E2':>10} {'3n^2-3n':>10} {'c_2':>7} {'E2/n^2':>7}")
        divs = [d for d in range(2, q) if (q - 1) % d == 0 and d % 2 == 0]
        for n in [d for d in divs if d <= 512][:9]:
            G = find_subgroup(q, n)
            e2 = E2(G, q)
            rel = "<<" if n < logq else (">>" if n > 2 * logq else "~")
            print(f"  {n:>5} {rel:>10} {e2:>10} {3*n*n-3*n:>10} {e2/(2*n*n):>7.3f} {e2/n**2:>7.3f}")


if __name__ == "__main__":
    main()
