"""Probe the THINNESS-ESSENTIAL autocorrelation identity (INV-B), exact over C.

  |eta_b|^2 = sum_{zeta in mu_n} eta_{b(zeta-1)}    (the zeta=1 term = eta_0 = n)

eta_b = sum_{x in mu_n} e_p(b x), e_p(t)=exp(2 pi i t / p), mu_n = order-n subgroup of F_p^*.
Uses that mu_n is a GROUP (x = zeta*y reindex). Tested on PROPER thin subgroups only
(m=(p-1)/n >= 2, never n=q-1), incl Fermat primes, multiple b.
"""
import cmath
import math


def find_subgroup(p, n):
    assert (p - 1) % n == 0

    def order(a):
        o = 1
        x = a % p
        while x != 1:
            x = (x * a) % p
            o += 1
        return o

    pr = None
    for a in range(2, p):
        if order(a) == p - 1:
            pr = a
            break
    h = pow(pr, (p - 1) // n, p)
    sub = []
    x = 1
    for _ in range(n):
        sub.append(x)
        x = (x * h) % p
    return sorted(set(sub))


def ep(t, p):
    return cmath.exp(2j * math.pi * (t % p) / p)


def eta(b, sub, p):
    return sum(ep((b * x) % p, p) for x in sub)


def test(p, n, label):
    sub = find_subgroup(p, n)
    assert len(sub) == n
    assert 0 not in sub
    m = (p - 1) // n
    assert m >= 2, "must be PROPER subgroup (never n=q-1)"
    maxerr = 0.0
    bs = [1, 2, 3, 5, 7, (p - 1) // 2, p - 2]
    for b in bs:
        if b % p == 0:
            continue
        lhs = abs(eta(b, sub, p)) ** 2
        rhs = 0.0 + 0j
        for zeta in sub:
            bb = (b * ((zeta - 1) % p)) % p
            rhs += eta(bb, sub, p)
        maxerr = max(maxerr, abs(lhs - rhs))
    print(f"{label}: p={p} n={n} m={m}  GROUP identity max|err|={maxerr:.2e}")
    return maxerr


print("=== |eta_b|^2 = sum_{zeta in mu_n} eta_{b(zeta-1)}  (thinness-essential, NON-MOMENT) ===")
errs = []
cases = [
    (257, 8, "Fermat p=257 n=8 m=32"),
    (97, 8, "p=97 n=8 m=12"),
    (113, 16, "p=113 n=16 m=7"),
    (193, 16, "p=193 n=16 Proth"),
    (257, 16, "Fermat p=257 n=16 m=16"),
    (641, 32, "p=641 n=32 m=20"),
    (65537, 16, "Fermat p=65537 n=16 deep"),
    (65537, 32, "Fermat p=65537 n=32"),
]
for p, n, lab in cases:
    if (p - 1) % n != 0:
        print(f"skip {lab}: n nmid p-1")
        continue
    errs.append(test(p, n, lab))
print(f"\nMAX ERROR over all PROPER subgroup cases: {max(errs):.2e}  -> "
      f"{'PASS' if max(errs) < 1e-6 else 'FAIL'}")
