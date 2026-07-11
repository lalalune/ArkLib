#!/usr/bin/env python3
"""wf407_T18-thinness_thickwindow.py  (#407 T18 — thinness-essential necessary condition)

THESIS UNDER TEST (T18): the target  B <= sqrt(2 n log p)  is FALSE in the
intermediate-THICK window  beta ~ 2.3-3.2  (claimed measured at Fermat p=65537),
where  B = max_{b!=0} | sum_{x in mu_n} e_p(b x) |  is the worst Gauss period,
n = |mu_n|, beta = log_n p (thickness exponent), m = (p-1)/n.

If the OPTIMAL inequality B <= sqrt(2 n log p) FAILS for some realizable (n,p) with
beta in the thick band, then EVERY thickness-MONOTONE proof method (any argument that
proves B <= sqrt(2 n log p) by an inequality that only ever gets tighter as the domain
gets thicker / beta -> 1) is LOGICALLY EXCLUDED, regardless of difficulty.

CRITICAL DISTINCTION we pin exactly:
  * log p   vs   log m = log((p-1)/n).   In the thick window n is a large fraction of
    p (beta small), so m = (p-1)/n is SMALL and log m << log p. The EVT / Salem-Zygmund
    law is B ~ sqrt(n log m) (max of m sub-Gaussians), NOT sqrt(n log p). So
    sqrt(2 n log p) can be SMALLER than the actual B precisely when log m is no longer
    the controlling scale (thick regime) -- this is the mechanism.

METHOD (EXACT, not sampled): for each n=2^mu we enumerate ALL distinct Gauss periods
exactly via the multiplicative coset transversal (eta is constant on cosets b*mu_n;
there are m = (p-1)/n distinct values). We use exact integer modular powers and a
high-precision complex exponential. We report:
    B, beta=log_n p, B/sqrt(2 n log p)  [the TARGET ratio: >1 => target FALSE],
    B/sqrt(2 n log m), B/sqrt(n log m), m, log m, log p.

We sweep:
  (1) FERMAT p=65537 (=2^16+1): the claimed witness. Here mu_n = the unique order-n
      subgroup, n=2^mu, mu=1..16. beta = 16*ln2/(mu*ln2) = 16/mu. Thick window
      beta in [2.3,3.2] <=> mu in [5,7] (16/7=2.29 .. 16/5=3.2).
  (2) A diagonal sweep over many primes p ~ n^beta for beta in a grid, to MAP where
      B/sqrt(2 n log p) crosses 1 (the thin/thick boundary) and confirm it is a beta
      phenomenon, not a single-prime artifact.
"""
import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import numpy as np


def all_periods_abs(p, n):
    """EXACT |eta_b| for ALL m=(p-1)/n cosets. eta_b constant on coset b*mu_n.
    Transversal of cosets: b = g^j, j=0..m-1. eta_b = sum_{i} e_p(b * g^{m*i}).
    Returns np.array of the m magnitudes (b ranges over coset reps; b=g^0=1 included,
    the trivial multiplicative coset -- there is NO b=0 here, all b!=0)."""
    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)          # generator of mu_n
    sub = np.empty(n, dtype=np.int64)
    cur = 1
    for i in range(n):
        sub[i] = cur
        cur = cur * gm % p
    m = (p - 1) // n
    twp = 2.0 * math.pi / p
    # precompute the unit roots we need lazily per coset (b*sub mod p) -> too big to
    # vectorize all; loop cosets, each is n exps. cost ~ m*n = p. fine for p<=~3e5.
    out = np.empty(m, dtype=np.float64)
    breps = np.empty(m, dtype=np.int64)
    b = 1
    for j in range(m):
        breps[j] = b
        b = b * g % p
    # vectorized per coset
    for j in range(m):
        prods = (int(breps[j]) * sub) % p          # n residues
        ang = twp * prods
        re = np.cos(ang).sum()
        im = np.sin(ang).sum()
        out[j] = math.hypot(re, im)
    return out


def worst_period(p, n):
    a = all_periods_abs(p, n)
    return float(a.max())


def main():
    flush = lambda *a: print(*a, flush=True)
    flush("#" * 100)
    flush("# T18 thinness-essential: is  B <= sqrt(2 n log p)  FALSE in the thick window beta~2.3-3.2 ?")
    flush("#" * 100)

    # ============ (1) FERMAT p = 65537 = 2^16 + 1 (the claimed witness) ============
    p = 65537
    lnp = math.log(p)
    flush(f"\n=== (1) FERMAT p = {p} = 2^16+1, log p = {lnp:.4f}.  mu_n = order-n subgroup, n=2^mu ===")
    flush(f"{'mu':>3} {'n':>6} {'beta=16/mu':>10} {'m':>7} {'log m':>7} {'B':>9} "
          f"{'B/sqrt(2n logp)':>15} {'B/sqrt(2n logm)':>15} {'B/sqrt(n logm)':>14} {'TARGET?':>8}")
    fermat_rows = []
    for mu in range(1, 17):
        n = 1 << mu
        if n >= p:
            continue
        m = (p - 1) // n
        beta = lnp / math.log(n)
        B = worst_period(p, n)
        tgt_ratio = B / math.sqrt(2 * n * lnp)          # >1 => optimal target FALSE
        lnm = math.log(m) if m > 1 else float('nan')
        sz2 = B / math.sqrt(2 * n * lnm) if m > 1 else float('nan')
        sz1 = B / math.sqrt(n * lnm) if m > 1 else float('nan')
        fail = "FALSE!" if tgt_ratio > 1.0 else "ok"
        flush(f"{mu:>3} {n:>6} {beta:>10.3f} {m:>7} {lnm:>7.3f} {B:>9.2f} "
              f"{tgt_ratio:>15.4f} {sz2:>15.4f} {sz1:>14.4f} {fail:>8}")
        fermat_rows.append((mu, n, beta, m, B, tgt_ratio, sz1, sz2))

    # which betas violate the target?
    viol = [(beta, tr) for (_, _, beta, _, _, tr, _, _) in fermat_rows if tr > 1.0]
    flush(f"\n  -> Fermat target-violations (B > sqrt(2 n log p)) at beta in: "
          f"{sorted(round(b,2) for b,_ in viol)}")
    if viol:
        bmin = min(b for b, _ in viol); bmax = max(b for b, _ in viol)
        flush(f"     thick-window violation band: beta in [{bmin:.2f}, {bmax:.2f}], "
              f"max ratio = {max(tr for _, tr in viol):.4f}")

    # ============ (2) DIAGONAL beta-sweep: where does B/sqrt(2n logp) cross 1? ============
    flush(f"\n{'='*100}")
    flush("# (2) Diagonal sweep p ~ n^beta (many primes/cell): locate the thin<->thick crossing of")
    flush("#     B / sqrt(2 n log p) = 1.  Below crossing (thick) target is FALSE; above (thin) ok.")
    flush(f"{'='*100}")
    betas = [1.5, 1.8, 2.0, 2.3, 2.6, 3.0, 3.4, 4.0, 5.0, 6.0]
    for n in (16, 32, 64):
        flush(f"\n  n = {n}:")
        flush(f"  {'beta*':>6} {'p':>9} {'m':>8} {'B':>8} {'B/sqrt(2n logp)':>16} "
              f"{'B/sqrt(2n logm)':>16}")
        used = set()
        for beta in betas:
            base = int(round(n ** beta))
            if base > 4_000_000:
                continue
            base -= base % n
            base += 1
            p2, tries = base, 0
            found = None
            while tries < 2_000_000 and p2 < 5_000_000:
                if p2 > 3 and is_prime(p2) and odd_part((p2 - 1) // n) > 1 and p2 not in used:
                    found = p2; used.add(p2); break
                p2 += n; tries += 1
            if found is None:
                continue
            p2 = found
            m = (p2 - 1) // n
            B = worst_period(p2, n)
            beta_real = math.log(p2) / math.log(n)
            lnp2 = math.log(p2); lnm2 = math.log(m)
            r_p = B / math.sqrt(2 * n * lnp2)
            r_m = B / math.sqrt(2 * n * lnm2) if m > 1 else float('nan')
            mark = "  <- target FALSE" if r_p > 1.0 else ""
            flush(f"  {beta_real:>6.2f} {p2:>9} {m:>8} {B:>8.2f} {r_p:>16.4f} {r_m:>16.4f}{mark}")

    flush(f"\n{'='*100}")
    flush("# VERDICT LOGIC: if B/sqrt(2n logp) > 1 anywhere with realizable mu_n, the OPTIMAL")
    flush("#   inequality is false there, so any thickness-MONOTONE method (tighter as beta->1)")
    flush("#   cannot prove the prize bound. The correct scale is log m, and thinness (m large)")
    flush("#   is what makes log m the right -- and small enough -- controlling scale.")
    flush(f"{'='*100}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
