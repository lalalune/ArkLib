#!/usr/bin/env python3
# REFUTATION HUNT: does the worst-case R = M/sqrt(n ln m) GROW with n along resonant primes?
# A resonance (n=64,p=7937: R=2.06) beat the typical 1.3-1.5. If max-over-primes R grows with n,
# the prize bound M <= C*sqrt(n log m) is FALSE for fixed C (the log-power is wrong / worst case
# unbounded). If max-R stays flat, the bound holds and resonances are bounded outliers.
import sympy, cmath, math

def supnorm_and_arg(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = [pow(h, j, p) for j in range(n)]
    m = (p - 1) // n
    w = 2 * math.pi / p
    mx = 0.0; argc = -1
    rep = 1
    for c in range(m):
        s = 0j
        for x in G:
            s += cmath.exp(1j * w * ((rep * x) % p))
        a = abs(s)
        if a > mx:
            mx = a; argc = c
        rep = (rep * g) % p
    return mx, m, argc

print(f"{'n':>5} {'#primes':>8} {'maxR':>7} {'meanR':>7} {'argmax (p,m,M/sqrtn,R)':>40}")
maxR_by_n = {}
for mu in range(3, 9):                      # n = 8..256
    n = 2 ** mu
    Rs = []
    best = (0.0, None)
    m = 2
    scanned = 0
    cap_p = 400000
    while n * m + 1 < cap_p and scanned < 400:
        p = n * m + 1
        if sympy.isprime(p):
            M, mm, _ = supnorm_and_arg(n, p)
            R = M / math.sqrt(n * math.log(mm))
            Rs.append(R)
            if R > best[0]:
                best = (R, (p, mm, M / math.sqrt(n), R))
            scanned += 1
        m += 1
    maxR_by_n[n] = best[0]
    print(f"{n:>5} {len(Rs):>8} {best[0]:>7.3f} {sum(Rs)/len(Rs):>7.3f}   {str(best[1]):>40}")

print()
ns = sorted(maxR_by_n)
print("max-R growth check (is it ~const, ~sqrt(log n), or worse?):")
for n in ns:
    print(f"  n={n:>4}: maxR={maxR_by_n[n]:.3f}   sqrt(ln ln p~): {math.sqrt(math.log(math.log(n*128))):.3f}")
# Fit maxR vs sqrt(log n): if ratio ~const, worst case ~ sqrt(n log m log n) (extra log)
print()
print("maxR / sqrt(log2 n)  (flat => worst-case carries an extra sqrt(log n) => bound needs it):")
for n in ns:
    print(f"  n={n:>4}: {maxR_by_n[n]/math.sqrt(math.log2(n)):.4f}")
