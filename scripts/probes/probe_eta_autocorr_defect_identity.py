r"""Probe the pointwise autocorrelation DEFECT identity, exact over C up to float error.

For a proper thin multiplicative subgroup mu_n < F_p^*:

    sum_{zeta in mu_n \ {1}} eta_{b(zeta-1)} = |eta_b|^2 - n

The prior group-shift identity includes the zeta=1 term eta_0=n. This probe checks the
consumer form directly, on PROPER thin subgroups only, never n=q-1, including Fermat-type
structured primes. It also checks the defect sum is real.
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
    assert pr is not None
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
    maxim = 0.0
    bs = [1, 2, 3, 5, 7, 11, (p - 1) // 2, p - 2]
    for b in bs:
        if b % p == 0:
            continue
        lhs = 0.0 + 0j
        for zeta in sub:
            if zeta == 1:
                continue
            lhs += eta((b * ((zeta - 1) % p)) % p, sub, p)
        rhs = abs(eta(b, sub, p)) ** 2 - n
        maxerr = max(maxerr, abs(lhs - rhs))
        maxim = max(maxim, abs(lhs.imag))
    print(f"{label}: p={p} n={n} m={m}  defect max|err|={maxerr:.2e} max|im|={maxim:.2e}")
    return maxerr, maxim


print("=== sum_{zeta != 1} eta_{b(zeta-1)} = |eta_b|^2 - n (proper thin mu_n only) ===")
cases = [
    (257, 8, "Fermat p=257 n=8"),
    (97, 8, "p=97 n=8"),
    (113, 16, "p=113 n=16"),
    (193, 16, "p=193 n=16 Proth"),
    (257, 16, "Fermat p=257 n=16"),
    (641, 32, "p=641 n=32"),
    (65537, 16, "Fermat p=65537 n=16 deep"),
    (65537, 32, "Fermat p=65537 n=32"),
]
errs = []
ims = []
for p, n, lab in cases:
    if (p - 1) % n == 0:
        e, im = test(p, n, lab)
        errs.append(e)
        ims.append(im)
print(f"\nMAX ERROR={max(errs):.2e}; MAX IM={max(ims):.2e} -> "
      f"{'PASS' if max(errs) < 1e-6 and max(ims) < 1e-6 else 'FAIL'}")
