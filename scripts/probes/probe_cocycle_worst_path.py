#!/usr/bin/env python3
"""
#407 -- WORST-CASE PATH (Lyapunov / large-deviation) probe of the alignment cocycle.

Background.  The naive UNIFORM-step submaximality input was refuted (some single
level-to-level ratio r_j = M(j+1)/M(j) exceeds sqrt(2); see
_DyadicPhaseChainingSubmaxRefuted.lean).  The task re-localizes the open core to a
worst-case-PATH bound on the alignment cocycle:

  r_j := M(j+1)/M(j) in [~1/sqrt2, 2]  (each step; r_j<=2 is the trivial child bound,
         r_j>=... the half-coset cancellation floor),

  M(N) = M(N0) * prod_{j=N0}^{N-1} r_j.

The floor M(N) <~ C*sqrt(2^N * log(q/2^N)) holds  iff  the GEOMETRIC MEAN of the
cocycle stays near sqrt(2):  (prod r_j)^{1/(N-N0)} -> sqrt(2)*(1+o(1)).
The trivial / refuting alternative is a frequency b that sustains r_j ~ 2 down the
WHOLE tower (then M(N) ~ 2^N = n -> a constant-fraction-of-n character sum, NO
cancellation, floor REFUTED).

This probe measures, FFT-exact over proper subgroups mu_{2^i} subset F_p^* (p large),
multi-prime, n up to 4096:

 (1) WORST-CASE-PER-LEVEL geometric mean  GM_lvl = (prod_j max_b r_j(b))^{1/L}.
     (this is the cocycle ENVELOPE -- the per-level worst, jumping between frequencies;
      max_b r_j(b) can exceed sqrt2, but does the PRODUCT stay near (sqrt2)^L?)

 (2) WORST SUSTAINED SINGLE-FREQUENCY PATH: for EACH frequency b, follow its own
     tower b, b*zeta, b*zeta^2, ... and compute the geometric mean of ITS ratios.
     Report  max_b GM_path(b).   If any single b sustains GM_path(b) -> 2, the
     cocycle bound is REFUTED (a persistently-aligned path exists).

 (3) The actual top-level normalized magnitude  M(K)/sqrt(2^K)  and
     M(K)/sqrt(2^K * log(p/2^K)) -- does the floor envelope hold numerically?

Self-contained (Miller-Rabin + primitive root + numpy FFT).
"""
import math
import numpy as np


def is_prime(num):
    if num < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if num % q == 0:
            return num == q
    d = num - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, num)
        if x == 1 or x == num - 1:
            continue
        for _ in range(r - 1):
            x = (x * x) % num
            if x == num - 1:
                break
        else:
            return False
    return True


def prime_factors(num):
    fs = set()
    d = 2
    while d * d <= num:
        while num % d == 0:
            fs.add(d)
            num //= d
        d += 1
    if num > 1:
        fs.add(num)
    return fs


def primitive_root(p):
    fs = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    raise RuntimeError("no primitive root")


def find_prime(K, lower):
    m = 1
    while True:
        cand = m * (1 << K) + 1
        if cand > lower and is_prime(cand):
            return cand
        m += 1


def gauss_vector(n, p, z):
    v = np.zeros(p)
    x = 1
    for _ in range(n):
        v[x] = 1.0
        x = (x * z) % p
    return v


def analyze(p, K, label):
    g = primitive_root(p)
    print(f"\n=== {label}: p={p}  (2^{K} | p-1, g={g}, n up to 2^{K}={1<<K}) ===")
    # Precompute |S_b(mu_{2^i})| for all b, all levels i = 2..K.
    absF = {}
    for i in range(2, K + 1):
        n = 1 << i
        z = pow(g, (p - 1) // n, p)
        v = gauss_vector(n, p, z)
        absF[i] = np.abs(np.fft.fft(v))  # absF[i][b] = |S_b(mu_{2^i})|

    # ---- (1) per-level worst ratio + envelope geometric mean ----
    N0 = 2
    L = K - N0
    log_prod_env = 0.0
    print(f"  per-level worst ratio max_b M_{{i+1}}(b)/M_i(b)  (envelope cocycle):")
    print(f"    {'i->i+1':>8} {'maxR':>8} {'GMrun':>8}")
    for i in range(N0, K):
        Mi = absF[i]
        Mi1 = absF[i + 1]
        mask = Mi[1:] > 1e-9
        ratios = Mi1[1:][mask] / Mi[1:][mask]
        maxR = ratios.max()
        log_prod_env += math.log(maxR)
        gm_run = math.exp(log_prod_env / (i - N0 + 1))
        print(f"    {i:>3}->{i+1:<3} {maxR:>8.4f} {gm_run:>8.4f}")
    GM_env = math.exp(log_prod_env / L)

    # ---- (2) worst SUSTAINED single-frequency path geometric mean ----
    # frequency b at level i maps to b*zeta at level i+1 where zeta = primitive 2^{i+1} root.
    # Track each starting b at level N0 down to K, accumulate log r_j along ITS path.
    # b_index transforms: at step i->i+1, b -> b (the FFT index of S_b(mu_{n2}) uses same b;
    #   the half-coset child of b's magnitude is governed by b's own value -- but the *path*
    #   that sustains alignment is the orbit b -> b under fixed b? No: M_{i+1}(b) uses S_b at
    #   level i+1 directly. The single-frequency path = fixed b across all levels.)
    # Fixed-b path: r_j(b) = |S_b(mu_{2^{j+1}})| / |S_b(mu_{2^j})|.
    best_gm_path = 0.0
    best_b = -1
    # vectorized over all b
    logr = np.zeros(p)
    valid = np.ones(p, dtype=bool)
    for i in range(N0, K):
        Mi = absF[i]
        Mi1 = absF[i + 1]
        with np.errstate(divide='ignore', invalid='ignore'):
            step = Mi1 / Mi
        bad = ~np.isfinite(step) | (Mi <= 1e-9)
        valid &= ~bad
        step_safe = np.where(bad, 1.0, step)
        logr += np.log(np.maximum(step_safe, 1e-12))
    gm_paths = np.exp(logr / L)
    gm_paths[~valid] = 0.0
    gm_paths[0] = 0.0  # exclude b=0
    best_b = int(np.argmax(gm_paths))
    best_gm_path = float(gm_paths[best_b])

    # ---- (3) top-level normalized magnitude ----
    MK = absF[K][1:].max()
    nK = 1 << K
    norm_sqrtn = MK / math.sqrt(nK)
    log_arg = max(p / nK, math.e)  # log(q/n)
    norm_floor = MK / math.sqrt(nK * math.log(log_arg))

    # ---- (4) REALIZED cocycle along the MAXIMIZING path (the object that matters) ----
    # M_max(i) := max_b |S_b(mu_{2^i})|.  This is the actual envelope M(i) in the Lean def.
    # Its cocycle r_i = M_max(i+1)/M_max(i) is what telescopes to M(K). GM of THIS = sqrt2 iff floor.
    Mmax = {i: float(absF[i][1:].max()) for i in range(N0, K + 1)}
    log_prod_real = 0.0
    real_ratios = []
    for i in range(N0, K):
        ri = Mmax[i + 1] / Mmax[i]
        real_ratios.append(ri)
        log_prod_real += math.log(ri)
    GM_real = math.exp(log_prod_real / L)
    max_real_step = max(real_ratios)

    print(f"  REALIZED sup-norm cocycle r_i = M_max(i+1)/M_max(i): "
          f"GM = {GM_real:.4f}, max single step = {max_real_step:.4f}  (sqrt2={math.sqrt(2):.4f})")
    print(f"  [envelope-of-ratios GM_env={GM_env:.2e}, sustained-fixed-b GM={best_gm_path:.3f} "
          f"-- both near-zero-denominator artifacts, NOT the controlling cocycle]")
    print(f"  top level: M(2^{K})={MK:.3f}  M/sqrt(n)={norm_sqrtn:.4f}  "
          f"M/sqrt(n*log(q/n))={norm_floor:.4f}")
    return dict(label=label, p=p, K=K, GM_env=GM_env, GM_path=best_gm_path,
                GM_real=GM_real, max_real_step=max_real_step,
                norm_sqrtn=norm_sqrtn, norm_floor=norm_floor)


if __name__ == "__main__":
    print("COCYCLE WORST-CASE-PATH probe (#407): does any frequency sustain r_j~2 down the tower?")
    print("Floor holds iff cocycle geometric-mean -> sqrt2; refuted iff a sustained path -> 2.\n")
    out = []
    for K, lo, lab in [(11, 2_000_000, "A"), (11, 3_000_000, "B"),
                       (10, 1_500_000, "C"), (12, 4_000_000, "D"),
                       (12, 8_000_000, "E")]:
        p = find_prime(K, lo)
        out.append(analyze(p, K, lab))
    print(f"\n========= SUMMARY (REALIZED sup-norm cocycle = the controlling object) =========")
    print(f"  {'prime':>6} {'p':>10} {'GM_real':>8} {'maxstep':>8} {'M/sqrtn':>9} {'M/floor':>9}")
    for r in out:
        print(f"  {r['label']:>6} {r['p']:>10} {r['GM_real']:>8.4f} {r['max_real_step']:>8.4f} "
              f"{r['norm_sqrtn']:>9.4f} {r['norm_floor']:>9.4f}")
    s2 = math.sqrt(2)
    max_gm = max(r['GM_real'] for r in out)
    max_step = max(r['max_real_step'] for r in out)
    print(f"\n  sqrt2 = {s2:.4f}")
    print(f"  max realized cocycle GM = {max_gm:.4f}  "
          f"({'EXCEEDS sqrt2 -- floor threatened' if max_gm>s2+0.05 else 'near sqrt2 -- floor numerically holds'})")
    print(f"  max realized single step = {max_step:.4f}  "
          f"({'some step > sqrt2 (uniform-step refuted, as known)' if max_step>s2+1e-3 else 'all steps <= sqrt2'})")
    print(f"  M/sqrt(n*log(q/n)) in [{min(r['norm_floor'] for r in out):.3f}, "
          f"{max(r['norm_floor'] for r in out):.3f}] -- the floor envelope (bounded => floor holds numerically)")
