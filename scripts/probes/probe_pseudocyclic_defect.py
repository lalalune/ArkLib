"""F9 pseudocyclic-defect probe (#444).

In a PSEUDOCYCLIC association scheme every nontrivial eigenvalue satisfies |eta|^2 = v EXACTLY
(the Ramanujan / prize bound). The cyclotomic scheme on mu_n (n-th roots of unity in F_p) is
*almost* pseudocyclic. This probe quantifies the DEFECT

    delta_j := |eta_j|^2 - n

over the m = (p-1)/n distinct cyclotomic PERIODS eta_j = sum_{x in mu_n} e_p(g^j x)
(periods are constant on cosets of mu_n, so there are exactly m distinct values).
Pseudocyclic  <=>  all delta_j == 0  <=>  M(n)^2 = max_j |eta_j|^2 = n exactly.

Prize-regime instances only: PROPER subgroups mu_n with p >> n^3 (NEVER the full group n=q-1).
No moment / energy route is used -- this is a direct spectral (DFT-of-indicator) measurement,
structurally distinct from the additive-energy faces.
"""
import math, time


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


def period_sqnorms(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    mu = [pow(g, (m * k) % (p - 1), p) for k in range(n)]
    two_pi_over_p = 2.0 * math.pi / p
    out = []
    for j in range(m):
        c = pow(g, j, p)
        re = 0.0
        im = 0.0
        for x in mu:
            ang = two_pi_over_p * ((c * x) % p)
            re += math.cos(ang)
            im += math.sin(ang)
        out.append(re * re + im * im)
    return out


def main():
    cases = [(97, 16), (193, 16), (257, 16), (769, 16), (1153, 16),
             (12289, 16), (40961, 16), (65537, 16),
             (193, 32), (12289, 32), (65537, 32)]
    header = (f"{'p':>8} {'n':>4} {'beta':>5} {'min_d':>10} {'max_d':>10} "
              f"{'M(n)^2':>10} {'C^2':>8} {'pseudoc':>8} {'sec':>6}")
    print(header, flush=True)
    for (p, n) in cases:
        if (p - 1) % n:
            continue
        t = time.time()
        sq = period_sqnorms(p, n)
        dt = time.time() - t
        d = [v - n for v in sq]
        mn = min(d)
        mx = max(d)
        m2 = n + mx
        c2 = m2 / (n * math.log(p / n))
        pc = "YES" if (mx - mn) < 1e-6 else "no"
        beta = math.log(p) / math.log(n)
        print(f"{p:>8} {n:>4} {beta:>5.2f} {mn:>10.3f} {mx:>10.3f} "
              f"{m2:>10.3f} {c2:>8.3f} {pc:>8} {dt:>6.2f}", flush=True)


if __name__ == "__main__":
    main()
