#!/usr/bin/env python3
"""
LANE L3 / R4 (#407) — FFT measurement of M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|
at PRIZE-SCALE constant-index primes p ~ n^beta (beta in [4,5]), n = 2^mu.

KEY SPEEDUP (per directive: "via FFT").  Let 1_H be the indicator vector of the
subgroup mu_n = H subset Z/p.  Then
   S_b = sum_{x in H} e_p(b x) = sum_{y in Z/p} 1_H(y) e^{2 pi i b y / p} = FFT(1_H)[b]
(up to sign convention).  ONE real-to-complex FFT of a length-p vector gives |S_b|
for ALL b in {1,...,p-1} at once, in O(p log p).  This reaches p ~ 10^8-10^9
(n up to 2^14-2^16 at beta=4) on a single machine, far beyond the O(p*n) direct
sweep.

We report, for each (mu, beta):
   n, p, beta_eff
   M(n)            = max_{b!=0} |S_b|                  [EXACT, full b-sweep via FFT]
   base            = sqrt(n*log(p/n))                  [the prize window scale]
   C   = M/base                                        [window-membership constant; LIVE question: bounded?]
   Cg  = M/sqrt(2*base^2)                              [the REFUTED sqrt(2) sharp comparison]
   meanS, p99S, p999S, p9999S                          [tail of the |S_b| distribution]
   nbig            = #{b : |S_b| > base}               [how many b exceed the window]
   argmax_b        = the maximizing b (for adversarial analysis)

Per directive (a): is C bounded as mu grows, or does it creep up?  Adversarial floor:
the FFT IS the exhaustive search -- the reported M is the TRUE global max over all b,
so any growth is REAL (not a sampling lower bound).
"""
import math, sys
import numpy as np
from sympy import isprime, primitive_root

def _p(*a):
    print(*a); sys.stdout.flush()

def find_prime_near(n, beta):
    """smallest prime p ≡ 1 mod n with p >= n^beta."""
    base = int(n**beta)
    p = base - (base % n) + 1
    if p <= base:
        p += n
    while not isprime(p):
        p += n
    return p

def subgroup_indices(p, n):
    """Indices (mod p) of the n-element subgroup mu_n of F_p^*."""
    g = int(primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    H = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        H[i] = x
        x = (x * h) % p
    assert len(set(H.tolist())) == n
    return H

def measure_fft(p, n):
    """EXACT M(n) and tail stats via one FFT of the indicator of mu_n."""
    ind = np.zeros(p, dtype=np.float64)
    H = subgroup_indices(p, n)
    ind[H] = 1.0
    F = np.fft.rfft(ind)          # F[b] = sum_y 1_H(y) e^{-2 pi i b y / p}, b=0..p//2
    mod = np.abs(F)
    # rfft gives b=0..floor(p/2); |S_b| = |S_{p-b}| (real input -> conj symmetry),
    # so the half-spectrum (excluding b=0) covers all distinct |S_b| values.
    modnz = mod[1:]               # drop b=0 (= n)
    base = math.sqrt(n * math.log(p / n))
    M = float(modnz.max())
    argmax = int(np.argmax(modnz)) + 1
    nbig = int((modnz > base).sum()) * 2   # each half-spectrum b pairs with p-b
    return {
        "M": M, "base": base, "argmax": argmax,
        "mean": float(modnz.mean()),
        "p99": float(np.percentile(modnz, 99)),
        "p999": float(np.percentile(modnz, 99.9)),
        "p9999": float(np.percentile(modnz, 99.99)),
        "nbig": nbig,
    }

def run(beta, mu_lo=6, mu_hi=15, pcap=600_000_000):
    _p(f"BETA {beta}  (prize-scale constant index, FFT exhaustive)")
    _p(f"{'mu':>3} {'n':>7} {'p':>14} {'beta':>6} {'M(n)':>10} {'base':>9} "
       f"{'C=M/base':>9} {'Cg=C/sq2':>9} {'mean':>7} {'p99':>7} {'p999':>7} "
       f"{'p9999':>8} {'#>base':>8} {'argmax_b':>10}")
    rows = []
    for mu in range(mu_lo, mu_hi + 1):
        n = 1 << mu
        p = find_prime_near(n, beta)
        if p > pcap:
            _p(f"{mu:>3} {n:>7} {p:>14}  -- skip (p>{pcap:,})")
            continue
        beta_eff = math.log(p) / math.log(n)
        r = measure_fft(p, n)
        C = r["M"] / r["base"]
        Cg = C / math.sqrt(2)
        _p(f"ROW b{beta} {mu:>3} {n:>7} {p:>14} {beta_eff:>6.3f} {r['M']:>10.2f} {r['base']:>9.2f} "
           f"{C:>9.4f} {Cg:>9.4f} {r['mean']:>7.2f} {r['p99']:>7.2f} {r['p999']:>7.2f} "
           f"{r['p9999']:>8.2f} {r['nbig']:>8d} {r['argmax']:>10d}")
        rows.append((mu, n, p, beta_eff, r["M"], r["base"], C))
    return rows

if __name__ == "__main__":
    # KB validation point: n=64, p=16778497 (claimed R = M/base = 1.051)
    p64, n64 = 16778497, 64
    r64 = measure_fft(p64, n64)
    _p("KBVAL n=64 p=16778497 (claimed C=1.051): "
       f"M={r64['M']:.3f} base={r64['base']:.3f} "
       f"C={r64['M']/r64['base']:.4f} Cg={r64['M']/r64['base']/math.sqrt(2):.4f} "
       f"argmax_b={r64['argmax']}")

    # beta=4 (H ~ p^{1/4}, the di Benedetto Thm 3.1 boundary) up to as high as feasible.
    run(beta=4.0, mu_lo=6, mu_hi=14, pcap=600_000_000)
    # beta=5 (H ~ p^{1/5} < p^{1/4} -- BELOW di Benedetto Thm 3.1 validity).
    run(beta=5.0, mu_lo=6, mu_hi=11, pcap=600_000_000)
    # beta=4.5 middle of the prize range.
    run(beta=4.5, mu_lo=6, mu_hi=12, pcap=600_000_000)
    _p("DONE")
