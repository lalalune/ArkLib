#!/usr/bin/env python3
# DOOR-IV Lane-1 follow-up (NON-redundant): does the prize ratio R(n)=M/sqrt(2 n log p) SATURATION
# (just shown flat in n at beta=4) HOLD ACROSS THE PRIZE BETA-BAND beta in [4,5], or does R worsen toward
# the upper prize end (beta=5)? The keff_beta_band probe measured K_eff (moment proxy); this measures the
# DIRECT object M (= the sup-norm) and its ratio R across beta. If R rises with beta, the saturation verdict
# must be qualified to the LOWER prize end; if R is flat in beta too, saturation is robust across the regime.
#
# Constraints: exact uint64 needs p < 2^32 (t*x < 2^64). beta=5 caps n at 64 (64^5 = 2^30 < 2^32).
# Proper mu_n < F_p*, p == 1 mod n, v2(p-1) = log2 n (good prime), NEVER n=q-1.
import math, numpy as np, time
def isp(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True
def proot(p):
    m = p-1; fs = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    g = 2
    while not all(pow(g, (p-1)//f, p) != 1 for f in fs): g += 1
    return g
def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def good_prime_near(n, target, cap=1<<32):
    mu2 = int(round(math.log2(n)))
    p = target + ((1 + n - target % n) % n)
    while p < cap:
        if p % n == 1 and isp(p) and v2(p-1) == mu2:
            return p
        p += n
    return None
def M_of_n(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p); m = (p-1)//n; gn = pow(g, n, p)
    mu = np.array([pow(h, j, p) for j in range(n)], dtype=np.uint64)
    P = np.uint64(p); c = 2.0*math.pi/p
    CH = 1 << 20
    tmpl = np.empty(min(CH, m), dtype=np.uint64); b = 1
    for j in range(len(tmpl)): tmpl[j] = b; b = b*gn % p
    gnCH = b
    best = 0.0; base = 1; i = 0
    while i < m:
        L = min(CH, m - i)
        bl = (tmpl[:L]*np.uint64(base)) % P
        re = np.zeros(L, dtype=np.float32); im = np.zeros(L, dtype=np.float32)
        for x in mu:
            t = ((bl*x) % P).astype(np.float32); ang = np.float32(c)*t
            re += np.cos(ang); im += np.sin(ang)
        mag = re*re + im*im
        v = float(math.sqrt(mag.max()))
        if v > best: best = v
        base = base*gnCH % p; i += L
    return best, m
def main():
    print("# DOOR-IV Lane-1: prize-ratio R=M/sqrt(2 n log p) ACROSS the prize beta-band [4,5] (good prime, p<2^32)")
    print("# does the (just-shown) n-saturation hold in beta too, or does R worsen toward beta=5?")
    for n in (16, 32, 48, 64):
        if not (n & (n-1) == 0):  # only true 2-powers are prize-faithful; skip 48
            continue
        row = []
        for beta in (4.0, 4.5, 5.0):
            target = int(round(n ** beta))
            if target >= (1 << 32): row.append((beta, None)); continue
            p = good_prime_near(n, target)
            if p is None: row.append((beta, None)); continue
            t0 = time.time(); M, m = M_of_n(n, p); dt = time.time()-t0
            beff = math.log(p)/math.log(n); R = M/math.sqrt(2.0*n*math.log(p))
            row.append((beta, R))
            print(f"  n={n:3d} beta={beta:.1f} (beff={beff:.2f}) p={p:>11} m={m:>8} M={M:7.2f} R={R:.4f} ({dt:.0f}s)", flush=True)
        Rs = [r[1] for r in row if r[1] is not None]
        if len(Rs) >= 2:
            print(f"   -> n={n}: R across beta = [{min(Rs):.3f},{max(Rs):.3f}], spread {max(Rs)-min(Rs):+.3f}", flush=True)
    print()
    print("  READ: spread ~0 (R flat in beta) => saturation is ROBUST across the prize regime [4,5].")
    print("        R rising with beta => saturation is only the LOWER prize end; upper end (beta=5) worse.")
    print("  NOT a CORE claim; n<=64 (beta=5 uint64 cap). CORE M<=C sqrt(n log(p/n)) stays OPEN.")
if __name__ == '__main__':
    main()
