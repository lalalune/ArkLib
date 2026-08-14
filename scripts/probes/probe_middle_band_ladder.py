#!/usr/bin/env python3
"""probe_middle_band_ladder.py — the monomial splitting ladder in the middle band (#357).

Extends probe_takeover_death_radius.py to agreements above m+1 (the open middle band
delta in [2/n, 1/2 - 1/n)). Findings at (16,4) and (16,8), p in {97,193}:

  * (16,4): a=10 (delta=0.375 = UDR): max #bad = 8 = n/2 at (X^10, X^8) — the e=2 rung;
            a >= 11 (delta < UDR): ZERO bad monomial pairs at both fields.
  * (16,8): a=12 (delta=0.25 = UDR): 4 = n/4 at (X^12, X^8) — the e=4 rung;
            a=13 (delta < UDR): zero; a=10 (delta=0.375, past Johnson 0.293):
            FIELD-DEPENDENT 80/72 — the Weil regime onset.

The ladder law: (X^{m+e}, X^m) with g = gcd(e,n) has bad set = -(mu_n)^e (size n/g),
witnesses = (a-g) opposite-coset points + the g crossings x^e = -lambda, reach
a <= m+g i.e. delta >= 1/2 - g/n; the optimal rung e = k/2 (n,k 2-powers) bottoms out
EXACTLY at the unique-decoding radius (n-k)/2n. Below UDR the monomial class is dead.
Run: python3 scripts/probes/probe_middle_band_ladder.py
"""
# (measurement driver identical to probe_takeover_death_radius.run with
#  a_list extended; kept as documentation of the recorded findings above)
from probe_takeover_death_radius import run
if __name__ == "__main__":
    for p in (97, 193):
        run(p, 16, 4, [13, 12, 11, 10], max_exp=15)
        run(p, 16, 8, [13, 12, 11, 10], max_exp=15)
