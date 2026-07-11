"""
probe_d3_timefreq.py — D3 lane (harmonic analysis & time-frequency) pre-screens for #444.

Target: M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)| <= C sqrt(n log(p/n)).
mu_n = order-n=2^mu subgroup of F_p*. We test whether several time-frequency tools give an
UPPER bound on M that (a) holds across (n,p) and (b) beats the L2/Johnson floor M ~ sqrt(n).

Each avenue produces a "certified bound" B(n,p) computed ONLY from the tool's mechanism, and we
report B / (sqrt(n log(p/n))) and B / sqrt(n). A bound that tracks sqrt(n log(p/n)) (ratio O(1),
not growing) and is genuinely < the trivial n SURVIVES. A bound caught at sqrt(n)*something-larger
or that needs M itself as input is REFUTED/circular.
"""
import math, numpy as np
from prize_workspace import Workspace, isprime, subgroup

def make_W(n, idx):
    # smallest prime p = n*m+1 with m >= idx
    for m in range(idx, idx*40):
        p = n*m + 1
        if isprime(p):
            return Workspace(n, p)
    return None

# grid: n = 2^mu power-of-two subgroups; idx ~ p/n target (beta scaling). Keep p enumerable in FFT.
GRID = []
for mu in range(3, 11):            # n = 8 .. 1024
    n = 2**mu
    for idx in (n, 4*n, 16*n):     # index m = p/n  ~ n, n^2, ... (beta ~ 2..3 small but trend visible)
        if n*idx*40 < 6_000_000:   # FFT length cap
            GRID.append((n, idx))

def header():
    print(f"{'n':>5} {'p':>9} {'M':>9} {'sqrtn':>7} {'M/sqn':>7} {'sqrt(n log(p/n))':>16} {'M/target':>9}")

def main():
    rows = []
    header()
    for n, idx in GRID:
        W = make_W(n, idx)
        if W is None: continue
        p = W.p
        M = W.M
        sqn = math.sqrt(n)
        target = math.sqrt(n * math.log(p/n))
        mag2 = W.mag2[1:]                # |eta_b|^2 over b!=0
        eta_abs = np.sqrt(mag2)
        N = len(mag2)                    # = p-1

        # --- Avenue HY: Hausdorff-Young / L^q exit. M <= ||eta||_q for all q>=2? trivially M=||.||_inf.
        # Useful bound: M^{2r} <= sum |eta|^{2r} = cumulant_r  => M <= cumulant_r^{1/2r}. depth r.
        # Best deterministic non-2nd-moment: minimize over r of (C_r)^{1/2r}. Test r up to ln(p).
        Cr_bound = min(
            (mag2 ** r).sum() ** (1.0/(2*r))
            for r in range(1, max(2, int(math.log(p)) ) + 1)
        )

        # --- Avenue BS: Beurling-Selberg / large-sieve majorant. The large-sieve (exact for
        # equispaced roots) gives sum_{b} |eta_b|^2 <= Delta * n with Delta = p (full group),
        # i.e. only Parseval => M <= sqrt(sum) = sqrt(n(p-1)) (vacuous). The *random-phase* LP
        # envelope it pins is sqrt(2 (p-1) ... ) — also vacuous. We record the L2-only ceiling.
        L2_ceiling = math.sqrt(mag2.sum())   # = sqrt(n(p-1)) Parseval; the BS/large-sieve gives this

        # --- Avenue BR: Bochner-Riesz / Cesaro-Riesz smoothing of the spectrum. Riesz mean of
        # order s: does a smoothed (band-limited) version of eta have smaller sup that controls M?
        # Test: sup of |Cesaro_W(eta)| with window W = n (the natural band). This is the
        # convolution of eta with a Fejer kernel of width n -> smooths but cannot exceed M by much.
        # We compute the Fejer-smoothed sup and report ratio to M (does smoothing kill the peak?).
        # eta over full p (with b=0 included) FFT-domain Fejer of width L:
        eta_full = W.eta
        L = n
        # Fejer weights in frequency (triangular) applied as multiplier:
        freqs = np.arange(p)
        tri = np.maximum(0.0, 1.0 - np.minimum(freqs, p-freqs)/L)
        smoothed = np.fft.ifft(np.fft.fft(eta_full) * tri)  # circular conv with triangular kernel
        BR_sup = float(np.abs(smoothed[1:]).max())

        # --- Avenue DEC: ell^2 decoupling heuristic. Bourgain-Demeter for a curve gives
        # ||sum f_theta||_{L^q} <~ (#caps)^{eps} (sum ||f_theta||^2)^{1/2} for q = critical.
        # For mu_n the "caps" = singleton roots; decoupling const ~ n^{eps}, so it yields
        # M <~ n^{1/2+eps} sqrt(log) at best — i.e. ESSENTIALLY the L2 floor (no phase gain).
        # We model the decoupling bound as sqrt(n)*n^{eps} with eps from the cap count, eps=0 ideal:
        DEC_bound = sqn * (n ** 0.0)   # ideal decoupling = sqrt(n); records "cannot beat L2".

        rows.append((n, p, M, sqn, M/sqn, target, M/target, Cr_bound, L2_ceiling, BR_sup, BR_sup/M))
        print(f"{n:>5} {p:>9} {M:>9.2f} {sqn:>7.2f} {M/sqn:>7.3f} {target:>16.2f} {M/target:>9.3f}")

    print("\n--- Avenue diagnostics (bound / target ratios; SURVIVES iff O(1) and < trivial n) ---")
    print(f"{'n':>5} {'p':>9} {'Cr^{1/2r}/M':>11} {'Cr/target':>10} {'L2ceil/M':>9} {'BRsup/M':>8}")
    for (n,p,M,sqn,_,target,_,Cr,L2c,BRs,brr) in rows:
        print(f"{n:>5} {p:>9} {Cr/M:>11.3f} {Cr/target:>10.3f} {L2c/M:>9.1f} {brr:>8.3f}")

if __name__ == "__main__":
    main()
