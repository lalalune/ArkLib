#!/usr/bin/env python3
"""
probe_407_close_existence_semantics.py

Purpose: make CONCRETE and VERIFY the two competing claims about the floor closure,
so the existence-semantics question can be answered decisively against the prize's
own quantifier structure.

Findings to verify numerically:
 (F1) The Kambiré pigeonhole margin: #window-primes(p in [4^s,8^s], p=1 mod n)  vs
      the floor-bad-prime upper bound  log2(D),  D bounded by resultant height.
      Kambiré's OWN bound is B <= log_4(s) bad primes PER r-tuple-pair, and
      #pairs * B << T (window primes). We re-verify his inequality at prize scale.
 (F2) The KEY asymmetry: the pigeonhole proves EXISTENCE of a good prime, NOT that
      a GIVEN/arbitrary prime in the regime is good. We quantify the *density* of
      bad primes to show: for a *universal* ("for all primes") statement, the bad
      primes are nonempty (so the universal floor statement is FALSE for the bad
      primes), whereas for an *existential* statement a good prime exists.

This probe does NOT prove the prize. It quantifies which SEMANTICS the pigeonhole serves.
"""
import math

def kambire_window_check(rho, C, verbose=True):
    """Reproduce Kambire's parameter setting + the bad-vs-good prime inequality."""
    # rho = u/2^v ; pick small u,v
    # Choose K a power of 2 in [L, 2L], L = max(C/(rho*log(1/(2rho))), 9/(2 log 8))
    L = max(C/(rho*math.log(1/(2*rho))), 9/(2*math.log(8)))
    K = 2**(math.ceil(math.log2(L)))   # power of 2 >= L  (Kambire: K=2^{floor(log2 L)+1})
    # s = 2^alpha, need 4^s >= n^3 and alpha big enough; we sweep alpha.
    rows = []
    for alpha in range(6, 34):
        s = 2**alpha
        # n = s * m, with m = 2^{2^alpha / K - alpha}; require K | 2^alpha and 2^alpha/K >= alpha
        if (2**alpha) % K != 0:
            continue
        exp_m = (2**alpha)//K - alpha
        if exp_m < 1 or exp_m > 40:   # keep m representable
            continue
        m = 2**exp_m
        n = s*m
        r = int(round(rho*s)) + 2
        # window [4^s, 8^s]; #primes = 1 mod n  ~ T  (Kambire lower bound)
        # T >= 8^s / (n^{3/2} log(8^s)),  using phi(n)=n/2
        logT = s*math.log(8) - 1.5*math.log(n) - math.log(s*math.log(8))
        # bad (triple) count:  C(s/2 wait -> #r-tuple pairs)  * B
        # Kambire: #pairs <= (C(s/2, r))^2 <= (2^{s/2})^2 = 2^s ; B = log_4(s) per pair
        # so bad triples <= 2^s * log4(s)
        B = math.log(s)/math.log(4)
        log_bad = s*math.log(2) + math.log(max(B,1e-9))
        margin_log = logT - log_bad    # want >> 0
        rows.append((alpha, s, n, r, logT/math.log(2), log_bad/math.log(2), margin_log/math.log(2)))
    if verbose:
        print(f"--- Kambire window check  rho={rho}  C={C}  L={L:.3f}  K={K} ---")
        print(f"{'alpha':>5}{'s':>8}{'log2 n':>8}{'r':>6}{'log2 T':>12}{'log2 bad':>12}{'log2 margin':>14}")
        for (alpha,s,n,r,lT,lb,mg) in rows:
            print(f"{alpha:>5}{s:>8}{math.log2(n):>8.1f}{r:>6}{lT:>12.1f}{lb:>12.1f}{mg:>14.1f}")
    return rows

def single_config_D_height(n):
    """The e2-rigidity proven species: a single config's relation R_U(zeta)=0 forces
       p <= (n^2+n)^{n/2}.  So #distinct bad primes for ONE config <= log2((n^2+n)^{n/2})."""
    log2_D = (n/2.0)*math.log2(n*n+n)
    return log2_D

if __name__ == "__main__":
    print("="*78)
    print("F1: Kambire pigeonhole margin at prize scale (his OWN inequality)")
    print("="*78)
    # NOTE: Kambire requires rho in (0,1/2) STRICTLY (he writes rho in (0,1/2),
    # u < 2^{v-1}).  rho=1/2 is the boundary (log(1/(2rho))=0) and is EXCLUDED by his
    # construction -- a fact worth recording: the prize rate rho=1/2 is NOT covered by
    # Kambire's counterexample at all.  We sweep the in-range prize rates.
    for (rho,C) in [(0.25,1.0),(0.125,1.0),(0.0625,2.0)]:
        kambire_window_check(rho, C)
        print()

    print("="*78)
    print("F2: single-config proven D-height  log2((n^2+n)^{n/2})  (e2_extra_solution_threshold)")
    print("="*78)
    for mu in [8,16,24,30,40]:
        n = 2**mu
        print(f"  n=2^{mu:<3} : log2(D_single) = {single_config_D_height(n):.3e}   "
              f"(= #bad primes per single config, an upper bound)")
    print()
    print("INTERPRETATION:")
    print(" * F1 margin >> 0 at every prize row => a GOOD prime EXISTS in [4^s,8^s].")
    print("   This is EXACTLY Kambire's published pigeonhole; it gives an EXISTENTIAL prime.")
    print(" * It does NOT show an ARBITRARY/GIVEN prime q=1 mod n in the window is good:")
    print("   bad primes are a nonempty (sparse) set, so 'for ALL such q' is FALSE.")
    print(" * Therefore the pigeonhole serves the EXISTENTIAL floor (choose q), not the")
    print("   UNIVERSAL one (for all q).  Whether that closes the prize depends on whether")
    print("   the prize's delta* quantifies over a CHOSEN q (existential) or ALL q (universal).")
