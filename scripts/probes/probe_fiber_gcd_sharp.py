"""Probe: r(c) = deg gcd(X^n-1, (1+X)^n - c^n) on THIN 2-power mu_n, p>>n^3, p==1 mod n.
Confirm the gcd is GENUINELY sharper than the degree-n bound (deg gcd << n in prize regime),
and that the fibre = common-root set of X^n-1 and the O213 shiftedPowPoly. NEVER n=q-1."""
import sympy
from sympy import GF, Poly, symbols, gcd as pgcd

X = symbols('X')


def repcount_fiber(p, n, c):
    # r(c) = #{w in mu_n : (1+w)^n = c^n}  (the O213 fibre form)
    cn = pow(c, n, p)
    cnt = 0
    g = sympy.primitive_root(p)
    base = pow(g, (p - 1) // n, p)  # generator of mu_n
    for k in range(n):
        w = pow(base, k, p)
        if pow((1 + w) % p, n, p) == cn:
            cnt += 1
    return cnt


def gcd_deg(p, n, c):
    K = GF(p)
    cn = pow(c, n, p)
    f = Poly(X**n - 1, X, domain=K)
    g = Poly((X + 1)**n - cn, X, domain=K)   # shiftedPowPoly (1+X)^n - c^n
    d = pgcd(f, g)
    return d.degree()


# p == 1 mod n and p >> n^3:
# n=8: n^3=512  -> 7681 (=1+8*960), 8161(=1+8*1020)
# n=16: n^3=4096 -> 12289(=1+16*768), 40961(=1+16*2560)
# n=32: n^3=32768 -> 104417(=1+32*3263), 270337(=1+32*8448)
primes_n = [(7681, 8), (8161, 8), (12289, 16), (40961, 16)]
print("%6s %4s %5s %5s %7s %5s sharper?" % ('p', 'n', 'c', 'r(c)', 'deggcd', 'deg=n'))
allmatch = True
for (p, n) in primes_n:
    assert (p - 1) % n == 0, (p, n)
    assert p > n**3, (p, n)
    # sweep ALL c in F_p* to find the MAX r(c) (the M-relevant worst case) and verify match
    maxr = 0
    maxr_c = None
    nsharp = 0
    ntot = 0
    for c in range(1, p):
        r = repcount_fiber(p, n, c)
        dg = gcd_deg(p, n, c)
        ok = (r == dg)
        allmatch &= ok
        ntot += 1
        if dg < n:
            nsharp += 1
        if r > maxr:
            maxr = r
            maxr_c = c
    r = repcount_fiber(p, n, maxr_c)
    dg = gcd_deg(p, n, maxr_c)
    print("%6d %4d %5d %5d %7d %5d max-r-case all-sharp=%s" %
          (p, n, maxr_c, r, dg, n, nsharp == ntot))
print("ALL r(c)==deg gcd over full F_p*:", allmatch)
