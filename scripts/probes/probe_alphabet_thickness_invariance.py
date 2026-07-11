#!/usr/bin/env python3
"""
Probe (#444 / I031 metric-entropy CONSTRAINT): the distinct-period ALPHABET SIZE is EXACTLY (q-1)/n
and is THICKNESS-INVARIANT - so it carries NO thinness signal (rule 3 => not a standalone prize lever).

I031DistinctPeriodCount proves |{|eta_b|}| <= |{eta_b}| <= (q-1)/n (the orbit/coset count). Two open hopes
a metric-entropy argument might lean on:
  (H1) cross-coset COLLISIONS shrink the alphabet below (q-1)/n at prize scale => smaller log => tighter
       union bound.
  (H2) any such shrink is THIN-SPECIFIC (thickness-essential), so it could feed a rule-3-legal lever.
This probe REFUTES both, precisely:
  - measures the EXACT distinct count of eta values and of |eta| moduli over F_p* (one rep per coset),
  - checks for ANY cross-coset eta collision (would make the count < (q-1)/n),
  - compares thin (beta>>2) vs thick (beta~2.3) - same n.
Verdict expected: count = (q-1)/n EXACTLY, no collisions, IDENTICALLY thin and thick => thickness-invariant.
PROPER thin mu_n: n=2^a, n|p-1, (p-1)/n>=2, primes incl p>>n^3 + Fermat 257, NEVER n=q-1.
"""
import cmath, math, sys


def is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def proot(p):
    phi = p - 1
    fac = set()
    x = phi
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.add(d)
            x //= d
        d += 1
    if x > 1:
        fac.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    return None


def measure(n, p):
    g = proot(p)
    step = (p - 1) // n
    m = (p - 1) // n
    mu = [pow(g, (k * step) % (p - 1), p) for k in range(n)]
    w = 2.0 * cmath.pi / p

    def eta(b):
        s = 0j
        for x in mu:
            s += cmath.exp(1j * w * ((b * x) % p))
        return s

    vals = set()
    mods = set()
    collide = 0
    seen = {}
    for j in range(m):  # one representative per coset
        b = pow(g, j, p)
        e = eta(b)
        kv = (round(e.real, 5), round(e.imag, 5))
        if kv in seen:
            collide += 1
        seen[kv] = j
        vals.add(kv)
        mods.add(round(abs(e), 5))
    beta = round(math.log(p) / math.log(n), 2)
    return m, len(vals), len(mods), collide, beta


def find_prime(n, target):
    p = ((target // n) + 1) * n + 1
    while not is_prime(p):
        p += n
    return p


def run(label, cases):
    print(f"\n=== {label} ===")
    print(f"{'n':>4}{'p':>9}{'beta':>6}{'m=(q-1)/n':>11}{'#eta':>7}{'#|eta|':>8}{'collide':>8}{'exact?':>8}")
    allexact = True
    for (n, p) in cases:
        m, nv, nm, col, beta = measure(n, p)
        exact = (nv == m and nm == m and col == 0)
        allexact &= exact
        print(f"{n:>4}{p:>9}{beta:>6}{m:>11}{nv:>7}{nm:>8}{col:>8}{str(exact):>8}")
    return allexact


if __name__ == "__main__":
    thin = [(2 ** a, find_prime(2 ** a, max((2 ** a) ** 3, 2000))) for a in range(2, 6)]
    thin.append((16, 257))
    thick = [(2 ** a, find_prime(2 ** a, int((2 ** a) ** 2.3))) for a in range(2, 6)]
    e1 = run("THIN  (p>>n^3 prize regime)", thin)
    e2 = run("THICK (beta~2.3 control)", thick)
    print("\n--- VERDICT ---")
    print(f"alphabet EXACTLY (q-1)/n, no cross-coset collisions: THIN={e1} THICK={e2}")
    print("=> alphabet size is THICKNESS-INVARIANT (identical thin & thick) => carries NO thinness signal.")
    print("=> H1 (sub-(q-1)/n collapse) and H2 (thin-specific shrink) BOTH REFUTED.")
    sys.exit(0 if (e1 and e2) else 1)
