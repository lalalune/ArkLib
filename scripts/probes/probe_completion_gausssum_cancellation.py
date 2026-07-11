"""
PROBE: is there NON-TRIVIAL cancellation among the t Gauss sums in the completion identity?

Completion identity (proven in tree): t * eta_psi(mu_n, b) = sum_{j=0}^{t-1} G_j,
  G_j = gaussSum(chi^{d j}, psi_b),  |G_j| = sqrt(q) for j != 0,  |G_0| = 1,  t = (q-1)/n.

O218 used the TRIANGLE bound |sum G_j| <= (t-1)sqrt(q)+1 => |eta| <= sqrt(q). The wall is that
the triangle inequality discards cancellation among the G_j. QUESTION (fresh, non-moment):
does |sum_j G_j| = t*|eta| exhibit cancellation FAR below the triangle bound (t-1)sqrt(q)?

If the realised |sum G_j| / ((t-1)sqrt q) ratio is BOUNDED AWAY from 1 (say <= rho < 1) UNIFORMLY
in the thin regime, that would be a NEW non-moment cancellation mechanism worth formalizing. If it
-> 1 (no uniform cancellation) OR if the cancellation is just the trivial sqrt(q)/((t-1)sqrt q) ~ 1/t
(i.e. |sum G_j| ~ t*|eta| ~ t*sqrt(q)... wait |eta|<=sqrt q so |sum|<= t sqrt q, and triangle gives
(t-1)sqrt q) -- need to compare |sum G_j| to BOTH t*sqrt(q) (trivial per-term cap is sqrt q each on
the WORST b) and (t-1)sqrt(q) (triangle). The interesting question: at the WORST b (max |eta|),
how does |sum G_j| compare to t*|eta_worst|? They're EQUAL by the identity. So the real question:
is |eta_worst| (hence |sum|/t) closer to sqrt(q) (no cancellation, wall) or to sqrt(n) (full
cancellation, PRIZE)? We already know from O218 it's ~ sqrt(q)(1 - n/q). So measure the RATIO
|eta_worst| / sqrt(q) and |eta_worst| / sqrt(n) across the thin regime to see WHICH scale it hugs.

NEVER n = q-1. PROPER thin mu_n, p == 1 mod n, multiple primes.
"""
import cmath, math

def primitive_root(p):
    phi = p - 1
    m = phi
    fac = []
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no gen")

def eta_worst(p, n):
    g = primitive_root(p)
    t = (p - 1) // n
    base = pow(g, t, p)
    mu = []
    v = 1
    for _ in range(n):
        mu.append(v)
        v = (v * base) % p
    w = cmath.exp(2j * math.pi / p)
    best = 0.0
    for b in range(1, p):
        s = sum(w ** ((b * x) % p) for x in mu)
        a = abs(s)
        if a > best:
            best = a
    return best, t

def run():
    cases = [
        (97, 4), (97, 8), (193, 8), (257, 16), (641, 16), (769, 16),
        (12289, 16), (12289, 32), (40961, 16), (40961, 32), (40961, 64),
        (65537, 16), (65537, 32), (65537, 64), (65537, 128),
    ]
    print(f"{'p':>7} {'n':>5} {'t':>6} {'|eta|w':>9} {'sqrtn':>8} {'sqrtq':>9} "
          f"{'e/sqn':>7} {'e/sqq':>7} {'beta':>5}")
    hugs_sqn = True
    for p, n in cases:
        if (p - 1) % n != 0:
            continue
        e, t = eta_worst(p, n)
        sqn = math.sqrt(n)
        sqq = math.sqrt(p)
        r_sqn = e / sqn
        r_sqq = e / sqq
        beta = math.log(p) / math.log(n)
        # "hugs sqrt(n)" if e/sqrt(n) stays O(1) bounded (prize), "hugs sqrt(q)" if e/sqrt(q) ~ 1
        print(f"{p:>7} {n:>5} {t:>6} {e:>9.4f} {sqn:>8.4f} {sqq:>9.4f} "
              f"{r_sqn:>7.3f} {r_sqq:>7.4f} {beta:>5.2f}")
    print()
    print("READ: if e/sqrtn column stays small+bounded (~ const) and e/sqrtq -> 0 as beta grows,")
    print("      then |eta_worst| HUGS sqrt(n) (prize scale) and the COMPLETION SUM exhibits")
    print("      near-FULL cancellation (|sum G_j| = t*|eta| ~ t*sqrt(n) << (t-1)sqrt(q)).")
    print("      That cancellation is REAL but is exactly the open BGK content (not a new lever")
    print("      unless its MECHANISM is structurally capturable). If e/sqrtn GROWS with beta,")
    print("      the cancellation is only partial. Empirics decide which.")

if __name__ == "__main__":
    run()
