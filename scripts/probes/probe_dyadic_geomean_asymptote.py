#!/usr/bin/env python3
"""
LANE: dyadic-transfer geomean ratio — ASYMPTOTIC trend vs the PRIZE-FLOOR-aware threshold.

Context. wf-A1 (_wf5A1_phase_transfer_spectral.lean) refuted the SUFFICIENT lemma
"per-level geomean of ratios rho_i := M(2^{i+1})/M(2^i) is <= sqrt(2)" by exhibiting ONE
countermodel: at p=67073, n=256 the geomean is ~1.5 > sqrt(2)=1.4142. That kills the pure
sqrt(n) law (M(2^L) <= M(1)*2^{L/2}).

BUT the PRIZE floor is WEAKER than the pure sqrt(n) law: it is
    M(n) <= C * sqrt(n * log(p/n)) = C * 2^{L/2} * sqrt(log(p/n)),
i.e. there is an EXTRA sqrt(log(p/n)) of slack on top of 2^{L/2}. Telescoping
M(2^L) <= M(1) * prod_i rho_i, the prize floor holds iff
    prod_i rho_i <= (C/M(1)) * 2^{L/2} * sqrt(log(p/n)),
i.e. iff the geomean
    rho_bar := (prod rho_i)^{1/L} <= sqrt(2) * [ (C/M(1)) * sqrt(log(p/n)) ]^{1/L}.

So the RIGHT threshold is NOT sqrt(2); it is sqrt(2) * slack^{1/L} where
slack = (C/M(1)) * sqrt(log(p/n)). The open question wf-A1 did NOT settle:

  Q. Does the worst-case geomean rho_bar APPROACH sqrt(2) as n=2^L grows (so that the
     log-slack^{1/L} factor absorbs the excess), or does it stay bounded ABOVE sqrt(2)
     by a constant (in which case telescoping is genuinely dead, even prize-floor-aware)?

We measure rho_bar(n,p) across a tower n=4..N for several primes in the prize band and
compare to BOTH thresholds: the strict sqrt(2) AND the prize-floor-aware
sqrt(2)*slack^{1/L}. PROBE-FIRST, PROPER mu_n (n=2^a, n|p-1, p>>n^3), NEVER n=q-1.

If rho_bar - sqrt(2) does NOT shrink with L (stays ~0.08-0.1), the telescoping lane is dead
even with the prize log-slack => a clean REFUTATION-with-mechanism for DISPROOF_LOG (the
dyadic transfer geomean is bounded away from sqrt(2), so per-level descent cannot reach even
the weaker prize floor). If it DOES shrink toward sqrt(2) fast enough, the lane is ALIVE and
worth formalizing the slacked threshold.
"""
import math
import numpy as np
from sympy import primitive_root, isprime


def subgroup(t, n, p):
    S = []
    x = 1 % p
    for _ in range(n):
        S.append(x)
        x = (x * t) % p
    return S


def M_of(n, p, g):
    """M(n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)| via FFT.
    Build indicator f of mu_n on Z/p; eta_b = sum_x e_p(b x) = conj(DFT)_b (since
    sum_x e_p(b x) = (DFT of indicator at -b)); |eta_b| = |FFT(f)[b]|. b=0 gives n,
    exclude it."""
    t = pow(g, (p - 1) // n, p)
    S = subgroup(t, n, p)
    f = np.zeros(p, dtype=np.float64)
    f[S] = 1.0
    F = np.fft.fft(f)
    mags = np.abs(F)
    mags[0] = 0.0  # b=0 term = n, excluded
    return float(mags.max())


def analyze(p, Lmax):
    g = int(primitive_root(p))
    # build the tower M(2),M(4),...,M(2^Lmax)
    Ms = {}
    a = 1
    while (1 << a) <= Lmax and (p - 1) % (1 << a) == 0:
        n = 1 << a
        # prize-regime guard: keep p >> n^3 (skip rungs that violate the band)
        if p <= n ** 3:
            break
        Ms[a] = M_of(n, p, g)
        a += 1
    return g, Ms


def main():
    sqrt2 = math.sqrt(2.0)
    # prize band: pick primes p ~ n^beta with beta in [4,5], p = 1 mod 2^a deep enough.
    # We want towers that go several levels while staying p >> n^3.
    cases = [
        # (p, Lmax_exponent) chosen so p-1 is highly 2-divisible and p>>n^3 over the tower
        (40961, 6),     # 40961 = 2^13*5 + 1 -> 2-adic val 13; n up to 2^6=64, 64^3=262144<40961? no
        (65537, 5),     # Fermat: 2^16+1; n up to 32, 32^3=32768<65537 ok
        (786433, 6),    # 786433 = 3*2^18 + 1; n up to 64, 64^3=262144<786433 ok
        (5767169, 7),   # 5767169 = 11*2^19 + 1; n up to 128, 128^3=2.1e6<5.7e6 ok
        (7340033, 7),   # 7340033 = 7*2^20 + 1; n up to 128 ok
    ]
    print("LANE: dyadic geomean rho_bar -- asymptote vs sqrt(2) and vs prize-floor-aware threshold")
    print("sqrt(2) =", round(sqrt2, 6))
    print()
    for p, Lmax_exp in cases:
        if not isprime(p):
            print(f"p={p} NOT prime, skip"); continue
        Lmax = 1 << Lmax_exp
        g, Ms = analyze(p, Lmax)
        levels = sorted(Ms)
        if len(levels) < 3:
            print(f"p={p}: tower too short ({len(levels)} rungs), skip"); continue
        print(f"=== p={p}  primitive_root={g}  rungs n=2^{levels[0]}..2^{levels[-1]} ===")
        # per-level ratios rho_i = M(2^{i+1})/M(2^i)
        rhos = []
        for i in levels[:-1]:
            if (i + 1) in Ms and Ms[i] > 1e-9:
                rhos.append(Ms[i + 1] / Ms[i])
        # cumulative geomean from the bottom up, and the prize threshold at each top level
        print("  n        M(n)     rho     rho_bar(cum)  thr_sqrt2  thr_prize(slacked)")
        prod = 1.0
        cnt = 0
        for idx, i in enumerate(levels):
            n = 1 << i
            line = f"  {n:<7d} {Ms[i]:8.4f}"
            if idx >= 1:
                rho = Ms[i] / Ms[i - 1]
                prod *= rho
                cnt += 1
                rho_bar = prod ** (1.0 / cnt)
                L = cnt  # number of doublings from the base rung levels[0]
                # prize-floor slack: C * sqrt(log(p/n)); take C=1, M(1)~M(base) absorbed in ratio base.
                logpn = math.log(p / n)
                slack = math.sqrt(max(logpn, 1e-9))   # C=1 conservative
                thr_prize = sqrt2 * (slack ** (1.0 / L))
                gap_s2 = rho_bar - sqrt2
                flag = "ABOVE both" if rho_bar > thr_prize else ("ok<prize, >sqrt2" if rho_bar > sqrt2 else "ok<sqrt2")
                line += f" {rho:7.4f} {rho_bar:11.4f}  {sqrt2:8.4f}  {thr_prize:8.4f}  [{flag}]"
            else:
                line += "    (base)"
            print(line)
        print()
    print("VERDICT KEY:")
    print("  If rho_bar stays > thr_prize(slacked) as n grows  => telescoping DEAD even prize-aware (REFUTATION).")
    print("  If rho_bar dips below thr_prize for large L         => prize-aware lane ALIVE; formalize slacked threshold.")
    print("  If rho_bar -> sqrt(2) monotonically                 => the log-slack^{1/L} window may open asymptotically.")


if __name__ == "__main__":
    main()
