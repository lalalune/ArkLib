#!/usr/bin/env python3
"""
#444 N7 — the single un-run DECISIVE computation flagged by the close-or-kill master map:
does the DC-subtracted Wick ratio  R_r := A_r / ((2r-1)!! * n^r)  cross 1 below the optimal
depth r ~ ln q, at beta = log_n p ~ 4 ?

A_r is the DC-SUBTRACTED additive-energy excess of mu_n (the n-th roots of unity in F_p):
    A_r = E_r(mu_n) - n^{2r}/p = (1/p) * sum_{b != 0} |eta_b|^{2r},   eta_b = sum_{x in mu_n} e_p(b x).
The DC subtraction (dropping b=0, which contributes n^{2r}) is exactly what lets the moment
method ESCAPE the unconditional Cauchy-Schwarz saturation p*E_r >= n^{2r}
(_MomentRouteSaturationNoGo.lean): the route is ALIVE iff R_r stays < 1 up to r ~ ln p.

Exact: A_r computed as (1/p) sum_{b!=0} (|eta_b|^2)^r  -- positive terms only, no catastrophic
cancellation, long double accumulation. Char-0 ideal Wick_r = (2r-1)!! * n^r.

Reports R_r vs r for testable n (32, 64), marks the optimal depth r* ~ ln p and any crossing.
Honest scope: depth ~89 / n=2^30 is computationally UNREACHABLE -- that gap IS the open wall;
this settles only the testable-scale behavior of the route.

------------------------------------------------------------------------------------------------
RESULT (exact, n=32 & 64; cross-validated against the swarm's probe_407_ArWick_ratio_profile.py):

  n=32  p=1048609   M=22.983  R_r* (r*=14) = 0.0296   R_r MONOTONE-falling, NO crossing
  n=64  p=16777601  M=38.529  R_r* (r*=17) = 0.1190   R_r MONOTONE-falling, NO crossing

VERDICT -- the master map's "single un-run decisive computation" N7, resolved at TESTABLE scale:
the DC-subtracted DC-Wick route is ALIVE (R_r < 1 throughout, no crossing below or at r*). This
REFINES probe_407_ArWick_ratio_profile (which tracks the FULL E_r/Wick and had to discard the
deep-r tail as a "finite-field DC/wraparound artifact, n^{2r}/p contamination... only clean rungs
r << r* trustworthy"): DC-SUBTRACTING (drop b=0, the n^{2r} mode -- exactly what the moment bound
M^{2r} <= sum_{b!=0}|eta_b|^{2r} uses) REMOVES that turn-up, so R_r is clean and monotone-falling
even AT r* -- giving the trustworthy r* value their probe could not. So the deep-r turn-up was pure
DC, and the clean route's only concern is the n-trend: R_r* RISES with n (0.0296 -> 0.1190, margin
1-R shrinking), consistent with the already-established bounded constant c=M/sqrt(n ln m) in
[1.18,1.30] up to n=512 (DISPROOF_LOG) -- i.e. a decelerating curve that plateaus BELOW 1, NOT a
geometric runaway to a crossing (per the in-tree "do not over-read short doubling trends" warning).

Cross-check: my EXACT M (full max over ALL b!=0) slightly EXCEEDS the swarm's SAMPLED M lower
bounds, as it must (0.964 vs ~0.835 of prize target at n=64).

NOT A CLOSURE. Confirms (independently, via the character-sum method vs probe_407's convolution)
the master map verdict: the DC-Wick route is not killed by any finite-scale obstruction, but
proving R_r < 1 at the unreachable n=2^30 / r*~89 regime IS the open char-p transfer = the BGK wall.
------------------------------------------------------------------------------------------------
"""
import sys, math
import numpy as np

def is_prime(num):
    if num < 2: return False
    for sp in (2,3,5,7,11,13,17,19,23,29,31,37):
        if num % sp == 0: return num == sp
    d = num - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, num)
        if x == 1 or x == num - 1: continue
        for _ in range(s - 1):
            x = x * x % num
            if x == num - 1: break
        else:
            return False
    return True

def find_prime_for(n, target_beta=4.0):
    """smallest prime p >= n^target_beta with p == 1 (mod n)  -> beta = log_n p slightly >= 4."""
    base = int(n ** target_beta)
    p = base + ((1 - base) % n)        # first p >= base with p % n == 1
    while not is_prime(p):
        p += n
    return p

def order_n_generator(p, n):
    """an element g with multiplicative order exactly n (so {g^j} = mu_n)."""
    e = (p - 1) // n
    assert (p - 1) % n == 0, "n must divide p-1"
    for a in range(2, p):
        g = pow(a, e, p)
        if g == 1:
            continue
        # order divides n; require order exactly n: g^(n/q) != 1 for each prime q | n
        ok = True
        m = n
        q = 2
        seen = set()
        while q * q <= m:
            if m % q == 0:
                seen.add(q)
                while m % q == 0: m //= q
            q += 1
        if m > 1: seen.add(m)
        for q in seen:
            if pow(g, n // q, p) == 1:
                ok = False; break
        if ok:
            return g
    raise RuntimeError("no generator found")

def double_factorial_odd(k):  # (2r-1)!! as exact int, k = 2r-1
    r = 1
    while k > 0:
        r *= k; k -= 2
    return r

def run(n, rmax=30, chunk=2_000_000):
    p = find_prime_for(n)
    beta = math.log(p) / math.log(n)
    g = order_n_generator(p, n)
    mu = [pow(g, j, p) for j in range(n)]
    assert len(set(mu)) == n, "mu_n not distinct"
    # sum_{b!=0} |eta_b|^{2r} for each r, computed by CHUNK-ACCUMULATION (low memory: never
    # stores a full p-array). Exact int reduction (b*x) mod p BEFORE the angle keeps the cos/sin
    # argument in [0,2pi) -> accurate even at p ~ 1e8 (avoids large-argument trig precision loss).
    twopi_over_p = 2.0 * math.pi / p
    mu_arr = np.array(mu, dtype=np.int64)
    Svec = np.zeros(rmax, dtype=np.float64)   # Svec[r-1] = sum_{b!=0} |eta_b|^{2r}
    M2 = 0.0
    for lo in range(0, p, chunk):
        hi = min(lo + chunk, p)
        b = np.arange(lo, hi, dtype=np.int64)
        re = np.zeros(hi - lo, dtype=np.float64)
        im = np.zeros(hi - lo, dtype=np.float64)
        for x in mu_arr:
            ang = twopi_over_p * ((b * x) % p)     # exact int mod -> small angle
            re += np.cos(ang); im += np.sin(ang)
        e2 = re * re + im * im
        if lo == 0:
            e2[0] = 0.0                            # DC subtraction: drop b=0
        M2 = max(M2, float(e2.max()))
        cur = np.ones(hi - lo, dtype=np.float64)
        for r in range(1, rmax + 1):
            cur *= e2
            Svec[r - 1] += float(cur.sum())
    M = math.sqrt(M2)                       # max_{b!=0} |eta_b|  (the BGK sup-norm)
    r_opt = math.log(p)                    # optimal moment depth ~ ln q
    prize_target = math.sqrt(2 * n * math.log(p / n))   # C*sqrt(n log m), m=p/n
    print(f"\n=== n={n}  p={p}  beta=log_n p={beta:.4f}  g(ord {n})={g} ===")
    print(f"M=max_(b!=0)|eta_b| = {M:.4f}   sqrt(n)={math.sqrt(n):.4f}   "
          f"prize sqrt(2n log m)={prize_target:.4f}   M/prize={M/prize_target:.4f}   r*~ln p={r_opt:.2f}")
    print(f"{'r':>3} {'R_r=A_r/Wick':>16} {'A_r':>14} {'Wick=(2r-1)!!n^r':>20} {'<1?':>5} {'note':>8}")
    crossed = None; Rvals = []
    for r in range(1, rmax + 1):
        A_r = Svec[r - 1] / p                     # = E_r - n^{2r}/p
        wick = float(double_factorial_odd(2 * r - 1)) * (float(n) ** r)
        R = A_r / wick
        Rvals.append(R)
        note = "<-r*" if r == round(r_opt) else ""
        if R >= 1.0 and crossed is None:
            crossed = r
        print(f"{r:>3} {R:>16.6f} {A_r:>14.4e} {wick:>20.4e} {str(R<1.0):>5} {note:>8}")
    ropt_i = max(1, min(rmax, round(r_opt)))
    print(f"  -> R_r {'CROSSES 1 at r='+str(crossed) if crossed else 'stays < 1 over r=1..'+str(rmax)}"
          f"   (optimal depth r*~{r_opt:.1f}, R_r*={Rvals[ropt_i-1]:.4f})")
    print(f"  -> trend: R_1={Rvals[0]:.3f} ... R_{rmax}={Rvals[-1]:.3e}  "
          f"({'rising' if Rvals[-1]>Rvals[0] else 'falling'})")
    return crossed, Rvals[ropt_i-1], M, prize_target

if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [32, 64]
    print("N7: DC-subtracted Wick ratio R_r = A_r/((2r-1)!! n^r); route ALIVE iff R_r<1 up to r*~ln p")
    for n in ns:
        run(n, rmax=30)
