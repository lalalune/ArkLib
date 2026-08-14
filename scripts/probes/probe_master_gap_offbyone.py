#!/usr/bin/env python3
"""
probe_master_gap_offbyone.py  (#444, lane mastergapfix)

Verify lalalune's 2026-06-16 AUDIT correction (deltastar-444-audit-corrections-2026-06-16.md, S.A.1):

  The widely-cited master gap identity  capacity - delta* = (m*-1)/n  is OFF BY ONE.
  The incidence-CORRECT binding radius is  delta* = 1 - s*/n  (delta-close  <=>  agreement >= (1-delta)*n),
  NOT  1 - (s*-1)/n  (the orbcount script-display convention).
  With the correct radius, the forced identity is  capacity - delta* = m*/n  (NOT (m*-1)/n).

This probe is PURE EXACT RATIONAL ARITHMETIC over the audit's own VERIFIED exact data
(s*, m*, delta* at n=8,16). It does NOT recompute the algebraic cascade (that is the audit's job,
already [VERIFIED] there). It confirms:

  (1) with delta* = 1 - s*/n and m* = s* - k, rho = k/n, the EXACT gap is m*/n (corrected), and
  (2) the OLD bricks' (m*-1)/n is exactly 1/n too SMALL (the off-by-one), and
  (3) the corrected gap m*/n REPRODUCES the audit's [VERIFIED] exact delta* (3/8 at n=8, 9/16 at n=16),
      whereas the (m*-1)/n form does NOT.

NEVER n=q-1: these are the thin prize-regime 2-power subgroup mu_n pins (n=2^a, rho=1/4, budget=n),
the audit's own VERIFIED rows. Field-universal Q arithmetic; thinness is in which (s*, m*) bind.
"""
from fractions import Fraction as F

# rho = k/n = 1/4 (the audit's regime: rate 1/4, budget = n). k = n/4.
# Audit's [VERIFIED] exact rows (deltastar-444-audit-corrections-2026-06-16.md, table in S.A):
#   n=8:  binding s*=5, m* = s*-k = 5-2 = 3, delta* = 3/8 = 0.375   (BELOW Johnson 1/2)
#   n=16: binding s*=7, m* = s*-k = 7-4 = 3, delta* = 9/16 = 0.5625 (ABOVE Johnson 1/2)
ROWS = [
    # (n, k, s_star, m_star_expected, deltaStar_audit_verified)
    (8,  2, 5, 3, F(3, 8)),
    (16, 4, 7, 3, F(9, 16)),
]

def report():
    print("=== probe: master gap identity off-by-one (audit S.A.1) ===")
    all_ok = True
    for (n, k, s, m_exp, dstar_audit) in ROWS:
        rho = F(k, n)                      # = 1/4
        capacity = 1 - rho                 # = 1 - rho
        m_star = s - k                     # m* = s* - k

        # CORRECT incidence convention: delta-close <=> agreement >= (1-delta)*n, so the binding
        # radius is delta* = 1 - s*/n.
        dstar_correct = 1 - F(s, n)
        gap_correct = capacity - dstar_correct       # should be m*/n

        # OLD (orbcount-label) convention: delta* = 1 - (s-1)/n  =>  gap = (m*-1)/n.
        dstar_old = 1 - F(s - 1, n)
        gap_old = capacity - dstar_old               # should be (m*-1)/n

        ok_mstar = (m_star == m_exp)
        ok_corr_gap = (gap_correct == F(m_star, n))
        ok_old_gap = (gap_old == F(m_star - 1, n))
        ok_corr_matches_audit = (dstar_correct == dstar_audit)
        ok_old_misses_audit = (dstar_old != dstar_audit)
        offby = dstar_old - dstar_correct            # the OLD radius is 1/n too LARGE => gap 1/n too small

        print(f"\n n={n}  k={k}  s*={s}  m*={m_star} (expect {m_exp})  rho={rho}  cap={capacity}")
        print(f"   CORRECT  delta* = 1 - s*/n     = {dstar_correct}   gap = cap-delta* = {gap_correct}  (m*/n = {F(m_star,n)})")
        print(f"   OLD      delta* = 1 - (s*-1)/n = {dstar_old}   gap = cap-delta* = {gap_old}  ((m*-1)/n = {F(m_star-1,n)})")
        print(f"   audit [VERIFIED] delta* = {dstar_audit}")
        print(f"   off-by:  delta*_old - delta*_correct = {offby}  (= 1/n = {F(1,n)})  [OLD over-states delta* by 1/n]")
        print(f"   checks:  m*={m_exp}:{ok_mstar}  corrGap=m*/n:{ok_corr_gap}  oldGap=(m*-1)/n:{ok_old_gap}  "
              f"corr==audit:{ok_corr_matches_audit}  old!=audit:{ok_old_misses_audit}  off==1/n:{offby==F(1,n)}")
        all_ok &= (ok_mstar and ok_corr_gap and ok_old_gap and ok_corr_matches_audit
                   and ok_old_misses_audit and offby == F(1, n))

    print("\n=== VERDICT ===")
    if all_ok:
        print("PASS: corrected gap = m*/n REPRODUCES the audit's exact delta* (3/8, 9/16);")
        print("      old gap = (m*-1)/n is exactly 1/n too small (off-by-one); old radius over-states delta* by 1/n.")
        print("      => the corrected master gap identity is  capacity - delta* = m*/n  (delta* = 1 - rho - m*/n).")
    else:
        print("FAIL: a check did not hold (see rows).")
    return all_ok

if __name__ == "__main__":
    import sys
    sys.exit(0 if report() else 1)
