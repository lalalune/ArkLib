#!/usr/bin/env python3
"""
probe_t1_charp_nonzero_ceiling.py  (#444 / #389 — OPEN THREAD T1-charp-ceiling-faithfulness)

THE ISOLATED PRIZE GAP, in its cleanest form.

M(mu_n) = max_{b!=0} |eta_b|,  eta_b = Sum_{x in mu_n} e_p(b x).  The DC-Wick moment ladder needs
the NONZERO-period energy to stay under the char-0 Wick ceiling:

    E_r^{Fp,nonzero} := (1/p) Sum_{b!=0} |eta_b|^{2r}  =  E_r^{Fp} - n^{2r}/p        (* identity *)
    ceiling_r        := (2r-1)!! * n^r                                              (char-0 Wick)
    R_r              := E_r^{Fp,nonzero} / ceiling_r                                (TARGET <= 1, or bounded K)

IDENTITY (*): Sum_{b=0}^{p-1} |eta_b|^{2r} = p * E_r^{Fp} (Parseval/char orthogonality of the r-fold
sumset count), and |eta_0|^{2r} = n^{2r} (b=0 character). So the b!=0 part divided by q=p is exactly
E_r^{Fp} - n^{2r}/p == the engine's "A_r". This probe measures R_r against the ceiling, NOT against
exact char-0 faithfulness (E_r^p == E_r^0): Avenue C established DCWickBound needs only the INEQUALITY
R_r <= 1 (it SURVIVES the upward anomaly E_r^p > E_r^0 as long as the NONZERO energy stays under the
char-0 Wick ceiling).

WHAT THIS PINS:
  (A) MARGIN at depth: ceiling - actual = (1 - R_r) * ceiling, at the ADVERSARIAL worst-in-window
      prime (generic primes understate the anomaly -> dishonest). r from 1..rmax, n=16..128.
  (B) THRESHOLD LAW T_r(n): smallest p (proper, p>n^3) above which R_r <= 1 holds, vs beta=log_n(p).
  (C) PRIZE VERDICT: at prize beta=4..5, does R_r <= 1 hold for all r up to r ~ log2(m) (the needed
      depth)? And is the b=0-spike (n^{2r}/p) what would push it over, or does removing it keep it under?

RULE-2: PROPER mu_n (n=2^mu, n | p-1, m=(p-1)/n >= 2, p > n^3, NEVER n=p-1).
RULE-1: EXACT integer convolution counts for E_r^{Fp}; rational n^{2r}/p kept exact (Fraction).
        => the integer comparison p*E_r^{Fp,nonzero} <= p*ceiling i.e. p*E_r^{Fp} - n^{2r} <= p*ceiling
        is a pure-integer decision (axiom-clean-able).
RULE-6: sub-prize n; maps the law + margin, does NOT prove the forall-field asymptotic (BGK wall).
Engines reused from probe_407_anom_worst_rtraj_n32.py (Ep exact mod-p convolution, roots_modp, is_prime).
"""
import sys, os, math
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, roots_modp, is_prime, doublefact_odd


def ceiling_int(n, r):
    return doublefact_odd(2 * r - 1) * (n ** r)


def proper_primes(n, beta_lo, beta_hi, cap):
    """PROPER in-window primes p=m*n+1, p in [n^beta_lo, n^beta_hi], m>=2, p>n^3."""
    lo = max(int(n ** beta_lo), n ** 3 + 1)
    hi = int(n ** beta_hi)
    out = []
    m = max(2, lo // n)
    while m * n + 1 <= hi and len(out) < cap:
        p = m * n + 1
        if p >= lo and p > n ** 3 and is_prime(p):
            out.append(p)
        m += 1
    return out


def Rr_at(mu, p, n, r):
    """R_r = (E_r^{Fp} - n^{2r}/p) / ((2r-1)!! n^r)   as an exact Fraction."""
    Ep_val = Ep(mu, p, r)                       # exact integer
    nonzero = Fraction(Ep_val) - Fraction(n ** (2 * r), p)   # E_r^{Fp,nonzero}, exact
    return nonzero / Fraction(ceiling_int(n, r)), Ep_val, nonzero


def worst_over_window(n, beta_lo, beta_hi, r, cap):
    """Adversarial: max R_r over proper in-window primes (worst = closest-to/over ceiling)."""
    ps = proper_primes(n, beta_lo, beta_hi, cap)
    if not ps:
        return None
    worst = None
    for p in ps:
        mu = roots_modp(n, p)
        R, Epv, nz = Rr_at(mu, p, n, r)
        if worst is None or R > worst[0]:
            worst = (R, p, Epv, nz)
    return worst, len(ps)


def main():
    print("=" * 104)
    print("T1: char-p NONZERO-period energy vs char-0 Wick ceiling.  R_r = (E_r^Fp - n^2r/p)/((2r-1)!! n^r)")
    print("TARGET R_r <= 1.  ADVERSARIAL = MAX R_r over proper in-window primes (generic understates anomaly).")
    print("identity: Sum_{b!=0}|eta_b|^2r / p = E_r^Fp - n^2r/p exactly. EXACT Fraction arithmetic.")
    print("=" * 104)

    # ---- (A) MARGIN PROFILE: worst-prime R_r across r, at prize-band beta in [4.0, 4.2] ----------
    print("\n(A) MARGIN PROFILE at prize band beta in [4.0,4.2]. R_r and (1-R_r) at the WORST proper prime.")
    print(f"    {'n':>4} {'r':>3} {'worst p':>14} {'beta':>5} {'E_r^Fp':>16} {'R_r':>10} "
          f"{'margin 1-R_r':>13} {'R_r<=1?':>8}")
    for n in [16, 32, 64, 128]:
        rmax = {16: 7, 32: 6, 64: 4, 128: 3}[n]
        for r in range(1, rmax + 1):
            # adaptive cap: fewer primes at deep r (each Ep convolution gets expensive)
            if n == 16:
                capn = 25
            elif n == 32:
                capn = 25 if r <= 5 else 6
            elif n == 64:
                capn = 12 if r <= 3 else 4
            else:
                capn = 4
            res = worst_over_window(n, 4.0, 4.2, r, cap=capn)
            if res is None:
                print(f"    {n:>4} {r:>3}  (no proper in-window prime)")
                continue
            (R, p, Epv, nz), npr = res
            beta = math.log(p) / math.log(n)
            Rf = float(R)
            ok = "YES" if R <= 1 else "NO!"
            print(f"    {n:>4} {r:>3} {p:>14} {beta:>5.2f} {Epv:>16} {Rf:>10.5f} "
                  f"{1 - Rf:>13.5f} {ok:>8}", flush=True)
        print()

    # ---- (B) THRESHOLD LAW T_r(n): smallest p with R_r<=1, vs depth r ----------------------------
    print("(B) THRESHOLD LAW. For fixed n,r: smallest PROPER prime p (p>n^3) with R_r<=1; beta_thresh=log_n p.")
    print(f"    {'n':>4} {'r':>3} {'smallest p, R_r<=1':>20} {'beta_thresh':>11} {'#primes<thresh w/ R_r>1':>22}")
    for n in [16, 32, 64]:
        rmax = {16: 7, 32: 6, 64: 4}[n]
        scancap = {16: 300, 32: 200, 64: 80}[n]
        for r in range(2, rmax + 1):
            # scan proper primes from just above n^3 upward; find first with R_r<=1
            lo_m = max(2, (n ** 3 + 1) // n + 1)
            m = lo_m
            found_p = None
            n_over = 0
            scanned = 0
            while scanned < scancap and found_p is None:
                p = m * n + 1
                m += 1
                if p <= n ** 3 or not is_prime(p):
                    continue
                scanned += 1
                mu = roots_modp(n, p)
                R, _, _ = Rr_at(mu, p, n, r)
                if R <= 1:
                    found_p = p
                else:
                    n_over += 1
            if found_p is None:
                print(f"    {n:>4} {r:>3} {f'(none in {scancap} primes)':>20}")
            else:
                bt = math.log(found_p) / math.log(n)
                print(f"    {n:>4} {r:>3} {found_p:>20} {bt:>11.3f} {n_over:>22}", flush=True)
        print()

    # ---- (C) PRIZE VERDICT: R_r<=1 for all r up to needed depth ~log2(m), at beta 4 and 5 --------
    print("(C) PRIZE VERDICT. needed depth r_need ~ log2(m), m=(p-1)/n. Does R_r<=1 hold for ALL r<=r_need")
    print("    at the WORST proper prime in the band? Also: does removing the b=0 spike (n^2r/p) matter?")
    print(f"    {'n':>4} {'beta band':>11} {'worst p':>14} {'m':>10} {'r_need~log2 m':>13} "
          f"{'max r w/ R<=1':>13} {'all r<=r_need OK?':>17}")
    for (blo, bhi) in [(4.0, 4.2), (5.0, 5.2)]:
        for n in [16, 32]:
            rmax = {16: 7, 32: 6}[n]
            # n=32 at beta=5 => p~2^25; cap=6 to keep runtime bounded
            ps = proper_primes(n, blo, bhi, cap=6 if (n == 32 and blo >= 5.0) else (8 if blo >= 5.0 else 25))
            if not ps:
                print(f"    {n:>4} {f'[{blo},{bhi}]':>11}  (no proper prime)")
                continue
            # pick the single adversarial prime = the one breaking R_r<=1 at the shallowest r
            worst_p = None
            worst_maxok = None
            for p in ps:
                mu = roots_modp(n, p)
                maxok = 0
                for r in range(1, rmax + 1):
                    R, _, _ = Rr_at(mu, p, n, r)
                    if R <= 1:
                        maxok = r
                    else:
                        break
                if worst_maxok is None or maxok < worst_maxok:
                    worst_maxok = maxok
                    worst_p = p
            m_val = (worst_p - 1) // n
            r_need = max(2, round(math.log2(m_val)))
            ok = "YES" if worst_maxok >= min(r_need, rmax) else f"NO (only r<={worst_maxok})"
            cap_note = "" if rmax >= r_need else f"  [probe cap rmax={rmax}<r_need]"
            print(f"    {n:>4} {f'[{blo},{bhi}]':>11} {worst_p:>14} {m_val:>10} {r_need:>13} "
                  f"{worst_maxok:>13} {ok:>17}{cap_note}", flush=True)
        print()

    print("=" * 104)
    print("READ THE ROWS. R_r<=1 == NONZERO energy under char-0 Wick ceiling (the DCWickBound inequality).")
    print("If worst-prime R_r<=1 holds through r_need at beta>=4 => the prize inequality is empirically")
    print("clear at scale (still open as forall-field BGK). If it breaks shallow at the adversarial prime,")
    print("the b=0-spike-removal alone does NOT save it and the ceiling route needs the (2r-1)!!->K margin.")
    print("=" * 104)


if __name__ == "__main__":
    main()
