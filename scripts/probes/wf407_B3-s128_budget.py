#!/usr/bin/env python3
"""
wf407 / B3-s128 — THE THORNER-ZAMAN s=128 CEILING: budget arithmetic verdict.

Goal: pin EXACTLY what distinguishes "s=64 opened unconditionally (via Parseval)"
from "s=128 still needs Thorner-Zaman", in the KKH26 Lemma-2 good-prime mechanism.

The mechanism (KKH26ThornerZaman.lean + KKH26PolyFieldCeiling.lean):
  - prime field p = Theta(n^beta), p == 1 (mod n), n = 2^mu * m  (s = 2^mu).
  - we must AVOID `m_pairs` collision resultants, each a nonzero integer of abs <= M.
  - bad primes (>= n^beta dividing some resultant): <= m_pairs * log(M) / log(n^beta).
  - good prime exists iff  supply(n,beta) > bad_budget.
  - supply ~ n^{beta-1-o(1)}  is the [TZ24] analytic input (NOT in mathlib).

The "s=64 unconditional" claim is NOT about TZ supply (still needed) — it's that for
beta in the *faithful unconditional range of TZ* (beta > 12/5) the supply provably exists.
So the real lever is: which resultant bound M, and which beta-budget makes the inequality
hold so cleanly that the analytic supply can be replaced by an explicit/decidable finite
check OR by the already-formalized TZ-faithful-range statement.

We compare resultant bounds:
  M_coarse   = s^{s/2}     = (2^mu)^{2^{mu-1}}            [the original threshold]
  M_fixedr   = (2r)^{2^{mu-1}}                            [fixed-r form, KKH26FixedRResultantBound]
  M_parseval = 8^{phi(n)/2} = 2^{3n/4}  (per resultant)  [SidonResultantImproved, halved exp]
  M_landau   = sqrt(4^{h-1} * (4h)^h), h = 2^{mu-1}       [SharpResultantBound, Mahler/Landau]

and the pair count
  a       = 2^r * C(2^{mu-1}, r)      (signed data count)
  m_pairs = a^2                       (ordered distinct pairs upper bound)

We report log2 of M and the resulting bad-prime budget, and find for each s the smallest
beta at which a *decidable finite supply* could plausibly close it.
"""
import math
from math import comb, log, log2

def analyze(mu, r, beta):
    s = 2**mu
    h = 2**(mu-1)          # phi(2^mu) = 2^{mu-1} ; also the resultant exponent
    n = s                  # take m=1 (worst smooth modulus = pure 2-power), n = 2^mu
    phi = h

    # resultant bounds, in log2
    log2_M_coarse  = h * log2(s)               # log2(s^{s/2}) = h*mu
    log2_M_fixedr  = h * log2(2*r) if r > 0 else float('inf')
    log2_M_parseval = 0.75 * n                 # log2(2^{3n/4})
    # Landau (squared): |Res|^2 <= 4^{h-1}*(4h)^h ; so log2|Res| <= ((h-1)*2 + h*log2(4h))/2
    log2_M_landau  = ((h-1)*2.0 + h*log2(4*h)) / 2.0

    # signed-data / pair count
    a = (2**r) * comb(h, r) if r <= h else 0
    m_pairs = a*a
    log2_m = 2*log2(a) if a > 0 else float('inf')

    # bad-prime budget = m_pairs * log(M) / log(n^beta) = m_pairs * log2(M) / (beta*log2(n))
    def budget(log2M):
        return m_pairs * log2M / (beta * log2(n))

    return {
        'mu': mu, 's': s, 'r': r, 'beta': beta, 'h': h, 'n': n,
        'a': a, 'm_pairs': m_pairs, 'log2_m': log2_m,
        'log2_M_coarse': log2_M_coarse,
        'log2_M_fixedr': log2_M_fixedr,
        'log2_M_parseval': log2_M_parseval,
        'log2_M_landau': log2_M_landau,
        'budget_coarse': budget(log2_M_coarse),
        'budget_fixedr': budget(log2_M_fixedr),
        'budget_parseval': budget(log2_M_parseval),
        'budget_landau': budget(log2_M_landau),
    }

print("="*100)
print("BUDGET ARITHMETIC: bad-prime count vs resultant-bound choice")
print("For the good prime to exist, the TZ supply ~ n^{beta-1} must EXCEED these budgets.")
print("="*100)
# r ~ rho * s/2 ; take a representative deep r. Prize rho in {1/2,1/4,1/8,1/16}.
# The deepest (worst) is r near h = 2^{mu-1}. We sweep r.
for mu in [5, 6, 7, 8]:   # s = 32, 64, 128, 256
    s = 2**mu
    h = 2**(mu-1)
    print(f"\n--- s = 2^{mu} = {s}   (h = phi = {h}) ---")
    print(f"{'r':>4} {'beta':>5} {'log2(m_pairs)':>13} {'log2 M_coarse':>14} {'log2 M_pars':>12} {'log2 M_land':>12} "
          f"{'bud_coarse':>11} {'bud_pars':>11} {'bud_land':>10}")
    for r in [2, max(2,h//8), max(2,h//4), max(2,h//2)]:
        for beta in [2.5, 3.0, 5.0]:
            d = analyze(mu, r, beta)
            print(f"{r:>4} {beta:>5.1f} {d['log2_m']:>13.1f} {d['log2_M_coarse']:>14.1f} "
                  f"{d['log2_M_parseval']:>12.1f} {d['log2_M_landau']:>12.1f} "
                  f"{d['budget_coarse']:>11.2e} {d['budget_parseval']:>11.2e} {d['budget_landau']:>10.2e}")

print()
print("="*100)
print("KEY: required supply exponent.  supply ~ n^{beta-1}.  We need n^{beta-1} > budget.")
print("So we need (beta-1)*log2(n) > log2(budget).  Smallest beta closing each s at deep r=h/2.")
print("="*100)
for mu in [5,6,7,8]:
    s=2**mu; h=2**(mu-1); n=s
    r = max(2, h//2)
    # find smallest beta (continuous) such that (beta-1)*log2(n) > log2(budget_parseval(beta))
    # budget = m_pairs*log2M/(beta*log2 n).  Self-consistent in beta.
    a = (2**r)*comb(h,r); m_pairs=a*a; log2_m=2*log2(a)
    log2M_pars = 0.75*n
    log2M_land = ((h-1)*2.0 + h*log2(4*h))/2.0
    log2M_coarse = h*log2(s)
    def closes(beta, log2M):
        log2_budget = log2_m + log2M - log2(beta) - log2(log2(n))
        return (beta-1)*log2(n) > log2_budget, log2_budget
    rows=[]
    for tag,log2M in [('coarse',log2M_coarse),('parseval',log2M_pars),('landau',log2M_land)]:
        bsmall=None
        for beta in [x*0.01 for x in range(101, 3001)]:
            ok,_=closes(beta,log2M)
            if ok:
                bsmall=beta; break
        rows.append((tag,log2M,bsmall))
    print(f"\ns=2^{mu}={s}, r={r}, log2(m_pairs)={log2_m:.1f}:")
    for tag,log2M,bsmall in rows:
        faithful = (bsmall is not None and bsmall > 2.4)  # TZ unconditional faithful range beta>12/5
        print(f"  bound={tag:>9} log2M={log2M:>8.1f}  smallest beta closing = "
              f"{('%.2f'%bsmall) if bsmall else 'none<=30':>8}  "
              f"{'(in TZ-faithful range b>2.4: supply UNCONDITIONAL)' if (bsmall and bsmall<=2.4) else ('(needs b='+('%.2f'%bsmall)+' >2.4 OK if TZ effective there)' if bsmall else '')}")
