#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — FLOOR-CHECK / honesty control for the connected triple correlation kappa3(k,l).

The companion sweep (probe_dooriv_signed_6point_cumulant.py) found |kappa3|/sd3 hovering near the
sampling floor with THIN and thick INTERLEAVED at matched cap. Before drawing any verdict, this control
nails down whether the observed |kappa3| is (a) pure 1/sqrt(cap) sampling noise of a phase-incoherent
(white) field, or (b) a genuine signal. Two decisive checks:

  CHECK 1 (cap-scaling): on a FIXED (n,p), measure mean_k,l |kappa3| at increasing cap. A sampling-noise
  floor shrinks as 1/sqrt(cap); a real connected cumulant stays flat. (Definitive: the verdict in the
  white-field and connected-4 entries used exactly this "shrinks with N => noise" criterion.)

  CHECK 2 (i.i.d. control): replace the period field by an i.i.d. complex field with the SAME marginal
  variance (random phases, magnitude = the empirical |z| histogram) and recompute. If the period field's
  |kappa3| matches the i.i.d. control, the triple correlation carries NO phase structure.

EXACT complex arithmetic on the period field; the control uses a phase-randomized surrogate.
"""
import cmath, math, statistics, random

random.seed(444)

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def find_prime(n, beta):
    t = int(round(n**beta)); k0 = max(2, t//n)
    for dk in range(0, 600000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n and is_prime(p): return p
    return None

def subgroup(p, n):
    pm1 = p-1; f = {}; m = pm1; d = 2
    while d*d <= m:
        while m % d == 0: f[d] = 1; m //= d
        d += 1
    if m > 1: f[m] = 1
    def isg(g): return all(pow(g, pm1//q, p) != 1 for q in f)
    g = 2
    while not isg(g): g += 1
    h = pow(g, pm1//n, p); mu = []; c = 1
    for _ in range(n): mu.append(c); c = c*h % p
    return mu, g

def eta_c(b, mu, p):
    return sum(cmath.exp(2j*math.pi*((b*y) % p)/p) for y in mu)

def kap3_mean(zc, sd3, cap, K=12):
    vals = []
    Kk = min(K, cap//3)
    for k in range(1, Kk):
        for l in range(k+1, Kk+1):
            acc = 0+0j
            for j in range(cap):
                acc += zc[j]*zc[(j+k) % cap]*zc[(j+l) % cap]
            vals.append(abs(acc/cap)/sd3)
    return statistics.fmean(vals), max(vals)

def main():
    print("=== CHECK 1: cap-scaling of mean|kappa3|/sd3 (fixed n,p). Noise floor ~ 1/sqrt(cap). ===")
    print(f"{'n':>4} {'p':>11} {'cap':>7} {'1/sqrt(cap)':>12} {'mean|k3|/sd3':>13} {'max|k3|/sd3':>12} {'ratio_to_floor':>15}")
    for n, beta in [(32, 4.5), (64, 4.0)]:
        p = find_prime(n, beta); mu, g = subgroup(p, n); N = (p-1)//n
        # precompute full z up to max cap once
        maxcap = min(N, 24000)
        zfull = []; cur = 1
        for _ in range(maxcap):
            zfull.append(eta_c(cur, mu, p)); cur = cur*g % p
        for cap in (3000, 6000, 12000, 24000):
            if cap > maxcap: continue
            z = zfull[:cap]; m = sum(z)/cap; zc = [v-m for v in z]
            var = sum(abs(v)**2 for v in zc)/cap; sd3 = var**1.5
            meanv, maxv = kap3_mean(zc, sd3, cap)
            floor = 1.0/math.sqrt(cap)
            print(f"{n:>4} {p:>11} {cap:>7} {floor:>12.5f} {meanv:>13.5f} {maxv:>12.5f} {meanv/floor:>15.3f}")
        print()

    print("=== CHECK 2: period field vs phase-randomized i.i.d. surrogate (same |z| multiset) ===")
    print(f"{'n':>4} {'p':>11} {'cap':>7} {'period mean|k3|':>15} {'iid mean|k3|':>13} {'period/iid':>11}")
    for n, beta in [(32, 4.5), (64, 4.0)]:
        p = find_prime(n, beta); mu, g = subgroup(p, n); N = (p-1)//n
        cap = min(N, 16000)
        z = []; cur = 1
        for _ in range(cap):
            z.append(eta_c(cur, mu, p)); cur = cur*g % p
        m = sum(z)/cap; zc = [v-m for v in z]
        var = sum(abs(v)**2 for v in zc)/cap; sd3 = var**1.5
        pmean, _ = kap3_mean(zc, sd3, cap)
        # i.i.d. surrogate: same magnitudes, random independent phases
        mags = [abs(v) for v in z]
        random.shuffle(mags)
        zr = [mags[j]*cmath.exp(2j*math.pi*random.random()) for j in range(cap)]
        mr = sum(zr)/cap; zrc = [v-mr for v in zr]
        varr = sum(abs(v)**2 for v in zrc)/cap; sd3r = varr**1.5
        imean, _ = kap3_mean(zrc, sd3r, cap)
        print(f"{n:>4} {p:>11} {cap:>7} {pmean:>15.5f} {imean:>13.5f} {pmean/imean if imean else float('nan'):>11.3f}")

    print()
    print("VERDICT CRITERIA:")
    print(" CHECK1: if mean|k3|/sd3 ~ 1/sqrt(cap) (ratio_to_floor roughly constant ~1) => pure sampling")
    print("         noise, NO connected 3rd cumulant. If it stays FLAT as cap grows (ratio grows) => signal.")
    print(" CHECK2: if period/iid ~ 1 => the period field's triple correlation is indistinguishable from a")
    print("         phase-incoherent i.i.d. field => no door-(iv) phase structure at 3rd/6th order.")

if __name__ == "__main__":
    main()
