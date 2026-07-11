#!/usr/bin/env python3
"""
#444 — Is the period-polynomial discriminant disc(Ψ) a free "second side" lever, or is it
CLASS-FIELD-THEORY-FIXED (hence house-independent and a vacuous lower bound at the prize)?

Setup: p prime, n | (p-1), m = (p-1)/n. μ_n ⊂ F_p^* the order-n subgroup; its m cosets give the
Gaussian periods η_0..η_{m-1} = Σ_{z∈coset} ζ_p^z, roots of the degree-m period polynomial Ψ ∈ ℤ[T]
generating the degree-m subfield K of ℚ(ζ_p). house = M(μ_n) = max_i |η_i|.

CFT prediction (conductor–discriminant): disc(K) = p^{m-1}, and disc(Ψ) = [O_K:ℤ[η]]² · disc(K),
so  |disc(Ψ)| = p^{m-1} · f²   (f a positive integer; perfect-square cofactor after dividing p^{m-1}).

If TRUE, disc(Ψ) is FIXED by p,m alone (independent of house), so the §5 "disc lower bound ⇒ house
upper bound" lever yields only  house ≥ |disc|^{1/(m(m-1))}/2 = p^{1/m}·f^{...}/2 ≈ p^{1/m} → 1
at the prize (m≈2^128) — VACUOUS. The lever would then be PRUNED (not the missing second side).

We also report house/√(2n·ln m) to cross-check the conjectured sub-Gaussian house law.
"""
from math import gcd, isqrt, log, sqrt
import sympy
try:
    import mpmath as mp
except Exception:
    from sympy import mpmath as mp  # fallback

def primitive_root(p):
    # smallest primitive root mod p
    fac = sympy.factorint(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def periods_and_disc(p, n, dps):
    mp.mp.dps = dps
    m = (p - 1) // n
    g = primitive_root(p)
    sub = set(pow(g, (m * j) % (p - 1), p) for j in range(n))   # μ_n, order n
    # m cosets: representatives g^0..g^{m-1}
    cosets = []
    for i in range(m):
        rep = pow(g, i, p)
        cosets.append(sorted((rep * s) % p for s in sub))
    zeta = mp.e ** (2j * mp.pi / p)
    eta = []
    for C in cosets:
        eta.append(mp.fsum(zeta ** z for z in C))
    house = max(abs(e) for e in eta)
    # discriminant = prod_{i<j} (eta_i - eta_j)^2  (round to nearest integer)
    disc = mp.mpf(1)
    disc = mp.mpc(1)
    for i in range(m):
        for j in range(i + 1, m):
            disc *= (eta[i] - eta[j]) ** 2
    disc_re = mp.re(disc)
    disc_im = mp.im(disc)
    disc_int = int(mp.nint(disc_re))
    err = abs(disc - disc_int)
    return m, g, [complex(e) for e in eta], float(house), disc_int, float(err), float(abs(disc_im))

def perfect_square(x):
    if x < 0:
        return False, None
    r = isqrt(x)
    return (r * r == x), r

CASES = [
    (4, [13, 29, 53, 61]),
    (8, [41, 73, 89, 97]),
    (16, [97, 113, 193, 241]),
    (32, [97, 193, 257, 353]),
]

print(f"{'p':>5} {'n':>3} {'m':>3} | {'house':>8} {'sqrt(2n ln m)':>13} {'ratio':>6} | "
      f"{'|disc|=p^(m-1)*sq?':>20} {'f':>10} {'round_err':>10}")
print("-" * 100)
all_cft = True
for n, primes in CASES:
    for p in primes:
        if (p - 1) % n != 0:
            continue
        m = (p - 1) // n
        if m < 2 or m > 13:   # keep exact disc tractable; m=1 trivial
            continue
        dps = max(60, int(m * (m - 1) // 2 * log(p) / log(10)) + 40)
        m_, g, eta, house, disc_int, err, imerr = periods_and_disc(p, n, dps)
        adisc = abs(disc_int)
        pm1 = p ** (m - 1)
        divisible = (adisc % pm1 == 0)
        cof = adisc // pm1 if divisible else None
        is_sq, f = perfect_square(cof) if divisible else (False, None)
        cft_ok = divisible and is_sq
        all_cft &= cft_ok
        denom = sqrt(2 * n * log(m)) if m >= 2 else float('nan')
        ratio = house / denom if denom == denom and denom > 0 else float('nan')
        verdict = "YES" if cft_ok else ("div but not sq" if divisible else "NOT p^(m-1)|disc")
        print(f"{p:>5} {n:>3} {m:>3} | {house:>8.3f} {denom:>13.3f} {ratio:>6.3f} | "
              f"{verdict:>20} {str(f):>10} {err:>10.1e}")
print("-" * 100)
print(f"CFT prediction |disc(Psi)| = p^(m-1)*f^2  holds in ALL cases: {all_cft}")
print()
print("Interpretation if YES: disc(Psi) is FIXED by (p,m) via conductor-discriminant, INDEPENDENT")
print("of house. So a 'disc lower bound' gives house >= |disc|^{1/(m(m-1))}/2 = p^{1/m}*f^{1/binom}/2.")
print("At the prize m~2^128 ==> p^{1/m}~1 ==> VACUOUS. The disc-lever is therefore NOT the missing")
print("second (upper) side -- the house upper bound does NOT follow from disc, which is house-blind.")
