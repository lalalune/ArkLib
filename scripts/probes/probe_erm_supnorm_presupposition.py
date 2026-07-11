# Probe (#444): the ERM ratio R(r)=E_{r+1}/(n*E_r) and whether ERM-at-r PRESUPPOSES
# the sup-norm bound max|eta|^2 <= (2r+1)*n  (Shaw 17:00 prose, never formalized).
#
# In-tree fact: sum_b |eta_b|^{2r} = q*E_r(G) (moment identity). With lam_b=|eta_b|^2:
#   E_r = (1/q) sum_b lam_b^r ;  R(r) = E_{r+1}/(n E_r) = (sum lam^{r+1})/(n sum lam^r).
# Claim A: R(r) MONOTONE INCREASING in r (power-mean ratio).
# Claim B: R(r) -> max_b lam_b / n as r->inf (largest eigenvalue dominates).
# Consequence: ERM-at-r (R(r)<=2r+1) at the plateau <=> max lam <= (2r+1)*n = sup-norm wall.
import cmath, math
from sympy import primitive_root


def mu_n_spectrum(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    sub = []
    x = 1
    for _ in range(n):
        sub.append(x)
        x = (x * h) % p
    lam = []
    for b in range(1, p):
        s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in sub)
        lam.append(abs(s) ** 2)
    return lam


def energies(lam, q, rmax):
    return [sum(l ** r for l in lam) / q for r in range(0, rmax + 1)]


print("Claim A (monotone) + Claim B (R(r) -> maxlam/n):")
print(f"{'n':>4}{'p':>9}{'maxlam/n':>11}  R(r) r=1..8")
for (p, n) in [(193, 8), (257, 16), (769, 16), (1153, 32), (12289, 32), (40961, 64)]:
    if (p - 1) % n != 0:
        continue
    lam = mu_n_spectrum(p, n)
    maxlam = max(lam)
    E = energies(lam, p, 10)
    Rs = [E[r + 1] / (n * E[r]) for r in range(1, 9) if E[r] > 1e-9]
    mono = all(Rs[i] <= Rs[i + 1] + 1e-6 for i in range(len(Rs) - 1))
    rstr = " ".join(f"{x:6.3f}" for x in Rs)
    print(f"{n:>4}{p:>9}{maxlam / n:>11.4f}  {rstr}  mono={mono}")

print()
print("Consequence: R(r) approaches maxlam/n; ERM-at-r requires R(r)<=2r+1:")
for (p, n) in [(1153, 32), (12289, 32), (40961, 64)]:
    if (p - 1) % n != 0:
        continue
    lam = mu_n_spectrum(p, n)
    maxlam = max(lam)
    E = energies(lam, p, 14)
    print(f"n={n} p={p} maxlam={maxlam:.1f} maxlam/n={maxlam / n:.3f}")
    for r in range(1, 13):
        if E[r] > 1e-9:
            R = E[r + 1] / (n * E[r])
            thr = 2 * r + 1
            print(f"   r={r:2d}  R={R:7.3f}  2r+1={thr:3d}  ERM-ok={R <= thr}  R/(maxlam/n)={R / (maxlam / n):.3f}")
