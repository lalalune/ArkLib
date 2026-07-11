"""Probe: for c NOT in G+G (G = mu_n proper subgroup of F_p*), is
deg gcd(X^n-1, (c-X)^n-1) == 0 (gcd trivial), or can it have degree>0
with no roots in G?  Determines whether the STRONGER 'gcd-trivial off the
sumset' statement holds, or only the weaker 'no roots in G' / r(c)=0.
Seeded for reproducibility."""
import random
from math import comb

random.seed(20260617)


def norm(u, p):
    u = [x % p for x in u]
    while len(u) > 1 and u[-1] == 0:
        u.pop()
    return u


def deg(u, p):
    u = norm(u, p)
    return len(u) - 1


def poly_mod(a, b, p):
    a = norm(a, p)
    b = norm(b, p)
    db = deg(b, p)
    inv = pow(b[db], p - 2, p)
    r = a[:]
    while deg(r, p) >= db and not (len(norm(r, p)) == 1 and norm(r, p)[0] == 0):
        r = norm(r, p)
        dr = deg(r, p)
        if dr < db:
            break
        c = (r[dr] * inv) % p
        for i in range(db + 1):
            r[dr - db + i] = (r[dr - db + i] - c * b[i]) % p
        r = norm(r, p)
    return norm(r, p)


def gcd_poly(a, b, p):
    a = norm(a, p)
    b = norm(b, p)
    while not (len(b) == 1 and b[0] == 0):
        a, b = b, poly_mod(a, b, p)
    da = deg(a, p)
    inv = pow(a[da], p - 2, p)
    return [(x * inv) % p for x in a[:da + 1]]


def reprpoly(c, n, p):
    coeffs = [0] * (n + 1)
    for k in range(n + 1):
        coeffs[k] = (comb(n, k) * pow(c, n - k, p) * pow(-1, k)) % p
    coeffs[0] = (coeffs[0] - 1) % p
    return coeffs


def mult_order(g, p):
    o = 1
    x = g
    while x != 1:
        x = (x * g) % p
        o += 1
    return o


primes = [97, 193, 257, 337, 1153, 12289]
total_off = 0
total_deg_pos = 0
for p in primes:
    a = 1
    while (1 << a) < (p - 1):
        n = 1 << a
        if (p - 1) % n == 0:
            g = 2
            while mult_order(g, p) != p - 1:
                g += 1
            zeta = pow(g, (p - 1) // n, p)
            G = set(pow(zeta, i, p) for i in range(n))
            GpG = set((x + y) % p for x in G for y in G)
            offc = [c for c in range(p) if c not in GpG]
            random.shuffle(offc)
            bad = 0
            tot = 0
            for c in offc[:8]:
                xn = [(-1) % p] + [0] * (n - 1) + [1]
                rp = reprpoly(c, n, p)
                gg = gcd_poly(xn, rp, p)
                dg = len(gg) - 1
                tot += 1
                if dg != 0:
                    bad += 1
            total_off += tot
            total_deg_pos += bad
            print("p=%d n=%d |G|=%d |G+G|=%d : off-sumset c tested=%d, deg(gcd)>0 cases=%d"
                  % (p, n, len(G), len(GpG), tot, bad))
        a += 1
print("TOTAL off-sumset c tested=%d, deg(gcd)>0 cases=%d" % (total_off, total_deg_pos))
