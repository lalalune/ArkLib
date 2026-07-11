#!/usr/bin/env python3
"""
LANE L3 / R4 (a) (#407) — the mu-TREND of the window-membership constant
   C(n) = M(n) / sqrt(n*log(p/n)),   M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|,
for n = 2^mu, p ~ n^beta (constant index).  CENTRAL QUESTION (directive a):
is C bounded as mu grows, or does it creep up?  And is there an adversarial b with
|S_b| >> sqrt(n log(p/n)) (a FLOOR refutation)?

FEASIBILITY.  Exact M needs the full b-sweep.  ONE rfft of the length-p indicator of
mu_n gives all |S_b| in O(p log p), but stores ~p floats => caps at p <~ 3e8.  At the
prize beta=4..5, p=n^beta hits 3e8 already at mu=6..7, so exact M at the PRIZE beta is
only reachable for mu<=7.  To see the mu-TREND we therefore ALSO sweep LOWER beta
(2.0, 2.5, 3.0) which reach mu=9..14 exactly -- the random-like heuristic predicts
C -> sqrt(2*beta/(beta-1)) (a CONSTANT in mu at fixed beta), so a mu-trend at fixed
beta tests boundedness directly.  At the prize beta and large mu we report an
ADVERSARIAL SAMPLED max (a LOWER bound on M): if THAT already exceeds the window,
the floor is refuted; if it stays ~C*base, the window holds.

Heuristic baseline (Parseval: E|S_b|^2 = n exactly; sup of ~p/2 random-like |S_b|):
   M ~ sqrt(2 n log(p/2))  =>  C = M/sqrt(n log(p/n)) ~ sqrt(2 log(p) / log(p/n))
                                                      = sqrt(2*beta/(beta-1)).
   beta=2: C~2.00;  beta=2.5: C~1.83;  beta=3: C~1.73;  beta=4: C~1.63;  beta=5: C~1.58.
A measured C that PLATEAUS near these (constant in mu) => window-membership robust.
A measured C that GROWS with mu => creep (toward refutation of C=O(1)).
"""
import math, sys
import numpy as np
from sympy import isprime, primitive_root

def _p(*a):
    print(*a); sys.stdout.flush()

def find_prime_near(n, beta):
    base = int(round(n ** beta))
    p = base - (base % n) + 1
    if p <= base:
        p += n
    while not isprime(p):
        p += n
    return p

def subgroup_indices(p, n):
    g = int(primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    H = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        H[i] = x
        x = (x * h) % p
    return H

def M_exact_fft(p, n):
    """EXACT M via one rfft of the indicator of mu_n. Caps at p<~3e8."""
    ind = np.zeros(p, dtype=np.float64)
    ind[subgroup_indices(p, n)] = 1.0
    mod = np.abs(np.fft.rfft(ind))[1:]
    base = math.sqrt(n * math.log(p / n))
    return float(mod.max()), base, float(mod.mean()), float(np.percentile(mod, 99.99))

def M_adversarial(p, n, nsamp=3_000_000, seed=0):
    """LOWER bound on M via (i) random b, (ii) rational-approx loci b=round(p*j/D),
    (iii) a hill-climb. Used when p too big for exact FFT."""
    H = subgroup_indices(p, n).astype(np.int64)
    twopi = 2 * math.pi / p
    def Sabs_vec(bs):
        ph = (np.outer(bs, H) % p).astype(np.float64)
        ang = twopi * ph
        re = np.cos(ang).sum(axis=1); im = np.sin(ang).sum(axis=1)
        return np.sqrt(re * re + im * im)
    best = 0.0
    rng = np.random.default_rng(seed)
    CH = max(1, (1 << 22) // n); done = 0
    while done < nsamp:
        c = min(CH, nsamp - done)
        best = max(best, float(Sabs_vec(rng.integers(1, p, size=c, dtype=np.int64)).max()))
        done += c
    # rational-approx loci (peaks of incomplete sums)
    cand = []
    for D in range(1, 2001):
        for j in range(1, D):
            if math.gcd(j, D) == 1:
                cand.append((p * j) // D)
        if len(cand) > 300000:
            arr = np.array(cand, dtype=np.int64) % p; arr = arr[arr != 0]
            best = max(best, float(Sabs_vec(arr).max())); cand = []
    if cand:
        arr = np.array(cand, dtype=np.int64) % p; arr = arr[arr != 0]
        best = max(best, float(Sabs_vec(arr).max()))
    # short multiplicative hill-climb from best random starts
    for s in range(8):
        b = int(rng.integers(1, p)); cur = float(Sabs_vec(np.array([b]))[0])
        for _ in range(300):
            cand2 = np.array([(b + d) % p for d in (1,-1,2,-2,n,-n)] +
                             [(b * t) % p for t in (2,3,5,p-1)], dtype=np.int64)
            cand2 = cand2[cand2 != 0]
            v = Sabs_vec(cand2); k = int(v.argmax())
            if v[k] > cur: cur = float(v[k]); b = int(cand2[k])
            else: break
        best = max(best, cur)
    base = math.sqrt(n * math.log(p / n))
    return best, base

def run():
    _p("=" * 78)
    _p("R4(a): mu-trend of C = M(n)/sqrt(n log(p/n)).  heuristic plateau sqrt(2b/(b-1)):")
    _p("       beta=2:2.00  2.5:1.83  3:1.73  4:1.63  5:1.58")
    _p("=" * 78)

    PCAP = 3.0e8
    # EXACT sweeps at each beta, going as high in mu as p<=PCAP allows.
    for beta in [2.0, 2.5, 3.0, 3.5, 4.0, 5.0]:
        _p(f"\n--- beta={beta} (EXACT FFT, p<= {PCAP:.0e}) ---")
        _p(f"{'mu':>3} {'n':>6} {'p':>13} {'beta':>6} {'M':>9} {'base':>9} "
           f"{'C=M/base':>9} {'plateau':>8} {'mean':>7} {'p9999':>8}")
        plateau = math.sqrt(2 * beta / (beta - 1))
        for mu in range(5, 16):
            n = 1 << mu
            p = find_prime_near(n, beta)
            if p > PCAP:
                break
            be = math.log(p) / math.log(n)
            M, base, mean, p9999 = M_exact_fft(p, n)
            _p(f"{mu:>3} {n:>6} {p:>13} {be:>6.3f} {M:>9.2f} {base:>9.2f} "
               f"{M/base:>9.4f} {plateau:>8.3f} {mean:>7.2f} {p9999:>8.2f}")

    # ADVERSARIAL lower bound at the PRIZE beta for mu beyond exact reach.
    _p("\n" + "=" * 78)
    _p("R4(a) ADVERSARIAL floor at PRIZE beta=4 (p>PCAP): Madv = LOWER bound on M.")
    _p("If Madv/base already > plateau, the window FLOOR is refuted.")
    _p("=" * 78)
    _p(f"{'mu':>3} {'n':>7} {'p':>16} {'Madv':>9} {'base':>9} {'C_lb=Madv/base':>15} {'plateau':>8}")
    plateau4 = math.sqrt(2 * 4.0 / 3.0)
    for mu in range(8, 13):
        n = 1 << mu
        p = find_prime_near(n, 4.0)
        M, base = M_adversarial(p, n, nsamp=2_000_000, seed=mu)
        _p(f"{mu:>3} {n:>7} {p:>16} {M:>9.2f} {base:>9.2f} {M/base:>15.4f} {plateau4:>8.3f}")
    _p("DONE")

if __name__ == "__main__":
    run()
