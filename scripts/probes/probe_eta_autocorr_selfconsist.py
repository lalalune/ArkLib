"""Self-consistency ceiling from the proven pointwise autocorrelation identity.

From  |eta_b|^2 = sum_{zeta in mu_n} eta_{b(zeta-1)}, the triangle inequality gives
  M^2 <= n + (n-1)*M,   M = max_b |eta_b|,
hence the self-consistency ceiling  M <= ((n-1) + sqrt((n-1)^2 + 4n)) / 2.
This probe checks whether that ceiling is a CORE lever (~sqrt(n)) or a trivial wall (~n).
PROPER thin subgroups only (m=(p-1)/n>=2, never n=q-1).
"""
import cmath
import math


def find_subgroup(p, n):
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
    total = 0.0 + 0j
    for x in sub:
        total += ep((b * x) % p, p)
    return total


print("n  p     M_actual  sqrt(n)  M/sqrt(n)  selfconsist_ceil  ceil/sqrt(n)")
for p, n in [(257, 8), (97, 8), (193, 16), (257, 16), (641, 32), (65537, 16), (65537, 32)]:
    if (p - 1) % n != 0:
        continue
    sub = find_subgroup(p, n)
    M = 0.0
    for b in range(1, p):
        v = abs(eta(b, sub, p))
        if v > M:
            M = v
    ceil = ((n - 1) + math.sqrt((n - 1) ** 2 + 4 * n)) / 2
    print(f"{n:2d} {p:5d}  {M:7.3f}  {math.sqrt(n):6.3f}  {M/math.sqrt(n):6.3f}  "
          f"{ceil:14.3f}  {ceil/math.sqrt(n):.3f}")

print()
print("VERDICT: self-consistency ceil -> n-1 (LINEAR), trivially weaker than sqrt(n).")
print("The triangle inequality on the shift sum assumes all n-1 nontrivial shifts align at M")
print("(zero cancellation) => thickness-INVARIANT, = the trivial |eta|<=n. NOT a CORE lever.")
print("The wall is the cancellation IN the shift sum that the triangle bound discards.")
