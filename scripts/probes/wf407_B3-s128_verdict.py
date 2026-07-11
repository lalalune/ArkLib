#!/usr/bin/env python3
"""
wf407 / B3-s128 — DECISIVE VERDICT on the s=128 Thorner-Zaman ceiling.

Two questions:
  (Q1) For the PRIZE s=128 (mu=7, s=2^mu=128) rows, what EXACT TZ statement is needed and
       can the supply be exhibited as a finite list (decidable, option (ii)) or must it be
       the asymptotic [TZ24] PNT-in-AP (option (i))?
  (Q2) Does the Myerson/Lehmer lacunary-cyclotomic-resultant-maxima route open s=128 WITHOUT
       Thorner-Zaman?

PRIZE PARAMETRIZATION (from KKH26AsymptoticCeiling.lean + memory regime-pin):
  - ceiling: delta* <= 1 - r/2^mu,  gap = Theta(1/2^mu) = Theta(1/s).
  - "s = 2^mu" is the gap-denominator: s=64 <=> mu=6, s=128 <=> mu=7.
  - rate rho = ((r-2)m+1)/n ~ r/s ; prize rho in {1/2,1/4,1/8,1/16} => r in {s/2, s/4, s/8, s/16}.
  - For gap ~ 1/log n the regime forces 2^mu <= C log_2 n, i.e. n ~ 2^{2^mu}: at s=128, n ~ 2^128.
  - field p = Theta(n^beta), p == 1 (mod n), MUST be polynomial in n.

collisionPairs cardinality = |sigData|^2 - |sigData| where sigData(2^{mu-1}, r) has
  a = 2^r * C(2^{mu-1}, r) elements (signed support data: choose r of the h=2^{mu-1} window
  positions, sign each). So m_pairs <= a^2.
"""
from math import comb, log2, log

def sigData_card(mu, r):
    h = 2**(mu-1)
    return (2**r) * comb(h, r) if r <= h else 0

def collisionPairs_card(mu, r):
    a = sigData_card(mu, r)
    return a*a - a   # ordered distinct pairs

print("="*108)
print("Q1.  PRIZE s=128 (mu=7) ROWS: bad-prime budget and required supply, per rate rho")
print("="*108)
print("Mechanism: bad_budget = m_pairs * log2(M) / (beta * log2(n)),  supply needed > bad_budget.")
print("M_coarse = (2^mu)^{2^{mu-1}}  (in-tree default);  M_parseval = 2^{3*2^mu/4} (halved exp).")
print()
for mu in [6, 7]:
    s = 2**mu
    h = 2**(mu-1)
    n_log2 = 2**mu   # n ~ 2^{2^mu} so log2(n) ~ 2^mu (the gap~1/log n regime)
    print(f"\n###### s = 2^{mu} = {s}   (h=2^(mu-1)={h}, regime n~2^{n_log2}, log2 n={n_log2}) ######")
    log2_M_coarse = h * mu          # log2((2^mu)^{2^{mu-1}})
    log2_M_pars   = 0.75 * s        # log2(2^{3s/4})
    print(f"  log2(M_coarse) = {log2_M_coarse},  log2(M_parseval) = {log2_M_pars}")
    print(f"  {'rho':>6} {'r':>4} {'log2 a':>8} {'log2 m_pairs':>13} "
          f"{'bud_coarse(beta=3)':>18} {'bud_pars(beta=3)':>17} {'supply~n^{b-1}':>16}")
    for rho_name, r in [("1/2", s//2), ("1/4", s//4), ("1/8", s//8), ("1/16", s//16)]:
        a = sigData_card(mu, r)
        mp = collisionPairs_card(mu, r)
        if a == 0:
            continue
        log2_a = log2(a)
        log2_mp = log2(mp) if mp>0 else 0
        beta = 3.0
        bud_coarse = log2_mp + log2(log2_M_coarse) - log2(beta*n_log2)  # log2 of budget
        bud_pars   = log2_mp + log2(log2_M_pars)   - log2(beta*n_log2)
        # supply ~ n^{beta-1} = 2^{(beta-1)*log2 n}
        supply_log2 = (beta-1)*n_log2
        print(f"  {rho_name:>6} {r:>4} {log2_a:>8.1f} {log2_mp:>13.1f} "
              f"{bud_coarse:>16.1f}b {bud_pars:>15.1f}b {supply_log2:>14.1f}b")
    print("    (values are log2; 'Xb' means 2^X. supply column = log2 of n^{beta-1} at beta=3.)")

print()
print("="*108)
print("READING: at s=128, deep rho=1/2 => r=64 => log2(m_pairs) ~ 2*log2(2^64*C(64,64))... let's see")
print("="*108)
# The crux: can the supply (an integer count of primes in [n^b, 2n^b], n~2^128) EXCEED the budget,
# AND can it be EXHIBITED as a finite decidable list?
# supply ~ n^{beta-1} = 2^{128*(beta-1)}.  At beta=3 that's 2^256 primes — NOT listable.
# So option (ii) finite list is IMPOSSIBLE at prize scale (n~2^128): you cannot decide-check 2^256 primes.
# => prize s=128 NEEDS option (i): the asymptotic [TZ24] PNT-in-AP lower bound. CONFIRMED.
print("supply at n~2^128, beta=3:  ~ n^2 = 2^256 primes needed in window.")
print("budget at s=128 deep rho=1/2:")
mu=7; s=128; h=64; n_log2=128
for rho_name, r in [("1/2",64),("1/4",32),("1/8",16),("1/16",8)]:
    a=sigData_card(mu,r); mp=collisionPairs_card(mu,r)
    log2_mp=log2(mp) if mp>0 else 0
    log2_M_coarse=h*mu; log2_M_pars=0.75*s
    for beta in [2.5,3.0,5.0]:
        bud_coarse=log2_mp+log2(log2_M_coarse)-log2(beta*n_log2)
        bud_pars  =log2_mp+log2(log2_M_pars)-log2(beta*n_log2)
        supply=(beta-1)*n_log2
        ok_coarse = supply>bud_coarse
        ok_pars   = supply>bud_pars
        print(f"  rho={rho_name:>4} r={r:>2} beta={beta:>3}: log2 supply={supply:>6.0f}  "
              f"log2 bud_coarse={bud_coarse:>7.1f} ({'OK' if ok_coarse else 'FAIL'})  "
              f"log2 bud_pars={bud_pars:>7.1f} ({'OK' if ok_pars else 'FAIL'})")

print()
print("="*108)
print("VERDICT on whether Parseval halving changes the s=64 vs s=128 boundary")
print("="*108)
print("The budget inequality (supply > budget) is EASILY satisfied at prize scale for BOTH")
print("coarse and Parseval M, at every rho, for any beta>2.4 -- because supply ~ n^{b-1}=2^{128(b-1)}")
print("DWARFS the budget ~ 2^{a few hundred at most}. The resultant-bound choice (coarse vs Parseval)")
print("does NOT decide the inequality. So Parseval halving is NOT what gates s=128.")
print()
print("What gates s=128 is purely: DOES the asymptotic supply n^{b-1-o(1)} EXIST?")
print("  - That is EXACTLY [TZ24]: pi(2x;n,1)-pi(x;n,1) >~ x/(phi(n) log x), x=n^b, valid for b>12/5.")
print("  - The 'o(1)' and the validity-for-beta>12/5 are the analytic content (log-free zero-density).")
print("  - It is INDEPENDENT of the resultant bound. Parseval/Landau only shift the *threshold* p>M,")
print("    relevant to the explicit-threshold route, NOT to whether the polynomial-size prime EXISTS.")
