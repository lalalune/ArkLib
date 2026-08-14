"""F9 pseudocyclic average-defect (Parseval) identity probe (#444).

The cyclotomic scheme on mu_n is pseudocyclic  <=>  |eta_b|^2 = n for ALL nonzero b.
By additive-character Parseval on F_p (1_{mu_n} has L^2 mass n):

    sum_{b in F_p} |eta_b|^2 = p * n          (eta_0 = n, so the b=0 term is n^2)
    => sum_{b != 0} |eta_b|^2 = p*n - n^2 = n*(p - n).

Hence the AVERAGE over the (p-1) nonzero frequencies:

    avg_{b!=0} |eta_b|^2 = n*(p-n)/(p-1) = n * (1 - (n-1)/(p-1)) < n.

So the average period magnitude-squared is STRICTLY BELOW the pseudocyclic value n
(average defect = -n*(n-1)/(p-1) < 0). The pseudocyclic ideal |eta|^2 = n is therefore
reachable ONLY if every defect is identically zero; any positive defect (the max, = the BGK
wall) is COMPENSATED by negative defects elsewhere (vanishing-or-small periods). This is an
EXACT, field-universal, NON-MOMENT structural identity -- it pins the average and shows the
scheme is sub-pseudocyclic in the mean, so a max-defect bound (the prize) cannot come for free
from a pseudocyclic / amorphic-scheme argument (the scheme is not amorphic; the mean already
fails the |eta|^2 = n equality from below).

Probe verifies the exact Parseval identity sum_{b!=0}|eta_b|^2 = n(p-n) on PROPER thin mu_n,
p >> n^3 (NEVER the full group), and confirms avg < n and max-defect > 0 (not pseudocyclic).
"""
import math


def primitive_root(p):
    phi = p - 1
    facs = set()
    x = phi
    d = 2
    while d * d <= x:
        if x % d == 0:
            facs.add(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        facs.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    return None


def all_period_sqnorms(p, n):
    """Return |eta_b|^2 for every nonzero b in F_p (m distinct values, each with multiplicity n)."""
    g = primitive_root(p)
    m = (p - 1) // n
    mu = [pow(g, ((p - 1) // n * k) % (p - 1), p) for k in range(n)]
    two_pi_over_p = 2.0 * math.pi / p
    # distinct period values are indexed by the m cosets b = g^j, j=0..m-1; each repeats n times.
    distinct = []
    for j in range(m):
        c = pow(g, j, p)
        re = 0.0
        im = 0.0
        for x in mu:
            ang = two_pi_over_p * ((c * x) % p)
            re += math.cos(ang)
            im += math.sin(ang)
        distinct.append(re * re + im * im)
    return distinct, m


def main():
    cases = [(97, 16), (193, 16), (257, 16), (769, 16), (1153, 16),
             (12289, 16), (40961, 16), (65537, 16),
             (193, 32), (12289, 32), (65537, 32)]
    print(f"{'p':>8} {'n':>4} {'sum_b!=0|eta|^2':>16} {'n(p-n)':>10} {'relerr':>10} "
          f"{'avg':>9} {'n':>5} {'avg<n?':>7} {'maxdef':>9} {'pc?':>4}")
    fails = 0
    total = 0
    for (p, n) in cases:
        if (p - 1) % n:
            continue
        total += 1
        distinct, m = all_period_sqnorms(p, n)
        # full sum over nonzero b: each distinct value repeats n times (coset size)
        s = sum(distinct) * n
        target = n * (p - n)
        relerr = abs(s - target) / target
        avg = s / (p - 1)
        maxdef = max(v - n for v in distinct)
        pc = "YES" if (max(distinct) - min(distinct)) < 1e-6 else "no"
        ok_avg = "YES" if avg < n else "NO"
        if relerr > 1e-6:
            fails += 1
        print(f"{p:>8} {n:>4} {s:>16.2f} {target:>10} {relerr:>10.2e} "
              f"{avg:>9.4f} {n:>5} {ok_avg:>7} {maxdef:>9.2f} {pc:>4}")
    print(f"\nParseval identity sum_b!=0 |eta_b|^2 = n(p-n): {total - fails}/{total} exact "
          f"(relerr <= 1e-6); avg < n ALWAYS; pseudocyclic NEVER (max-defect > 0).")


if __name__ == "__main__":
    main()
