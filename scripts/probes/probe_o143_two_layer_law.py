# O143: THE TWO-LAYER LAW of the window census - char-0 vanishing sums + finite-spectrum
# characteristic-p surplus. Unifies O134 + O138/O139/O140/O141/O142 into one statement.
#
#   census_p(n, k, depth-1 row) = (char-0 layer reduced mod p)  +  (surplus layer),
#
#   * char-0 layer: subsets A of mu_n with e2(A) = 0 in Z[zeta_n] - classical vanishing
#     power sums of roots of unity (the Lam-Leung / de Bruijn #232 lane, now INSIDE the
#     window census);
#   * surplus layer: nonzero ONLY for p in the finite spectrum S(n,k) = primes dividing
#     some cyclotomic norm N(e2(A)) over the char-0-NONvanishing subsets (O141 principle).
#
# Measured instances (exact, asserts below):
#   (8,4):  char-0 EMPTY, max|N| = 1, S = {}     - row clean at EVERY prime;
#   (8,2):  char-0 = 10 subsets (two mu_4-cosets with e1 = 0 + eight near-antipodal
#           configs), 9 distinct e1 values; S = {} - so at EVERY p = 1 (mod 8):
#           #qualifying = 10 and census = 9, verified at p in {17,41,73,89,97,113,233,1009};
#   (16,4): char-0 EMPTY, S = 17 primes, max norm 4097 = 2^12+1   [O142];
#   (16,8): char-0 EMPTY, S = 17 primes, max norm 18433           [O141].
#
# Consequence: the window-interior badness of the adjacent-pair family decomposes into
# (i) a field-INDEPENDENT census governed by classical vanishing-sum classification -
# nonzero only when n/k is large relative to the constraint depth (rate 1/4 at n = 8: yes;
# all n = 16 rows: no), and (ii) a field-EXCEPTIONAL finite-prime layer priced by Mahler-
# measure-type norm growth. Both layers are computable; neither requires scanning primes.
from itertools import combinations
import cmath


def cyc_engine(n):
    half = n // 2

    def zp(j):
        j %= n
        v = [0] * half
        if j < half:
            v[j] = 1
        else:
            v[j - half] = -1
        return tuple(v)

    def add(u, v):
        return tuple(x + y for x, y in zip(u, v))

    def mul(u, v):
        out = [0] * (2 * half - 1)
        for i, x in enumerate(u):
            if x:
                for j, y in enumerate(v):
                    if y:
                        out[i + j] += x * y
        for i in range(2 * half - 2, half - 1, -1):
            out[i - half] -= out[i]
            out[i] = 0
        return tuple(out[:half])

    return zp, add, mul, tuple([0] * half)


def char0_layer(n, a):
    zp, add, mul, ZERO = cyc_engine(n)
    sols, e1s = 0, set()
    for A in combinations(range(n), a):
        s1, s2 = ZERO, ZERO
        for j in A:
            s1 = add(s1, zp(j))
            s2 = add(s2, zp(2 * j))
        if tuple(x - y for x, y in zip(mul(s1, s1), s2)) == ZERO:
            sols += 1
            e1s.add(s1)
    return sols, len(e1s)


def norm_spectrum(n, a):
    ROOTS = [cmath.exp(2j * cmath.pi * j / n) for j in range(n)]
    UNITS = [t for t in range(n) if t % 2 == 1]
    vals = set()
    for A in combinations(range(n), a):
        prod = 1.0 + 0j
        for t in UNITS:
            s1 = sum(ROOTS[(t * j) % n] for j in A)
            s2 = sum(ROOTS[(2 * t * j) % n] for j in A)
            prod *= (s1 * s1 - s2) / 2
        v = round(prod.real)
        assert abs(prod.imag) < 1e-6 and abs(prod.real - v) < 1e-3, (A, prod)
        if v:
            vals.add(abs(v))
    def primes_of(m):
        fs, d = set(), 2
        while d * d <= m:
            while m % d == 0:
                fs.add(d)
                m //= d
            d += 1
        if m > 1:
            fs.add(m)
        return fs
    spec = set()
    for v in vals:
        spec |= primes_of(v)
    return sorted(p for p in spec if p % n == 1), (max(vals) if vals else 0)


# (8,4): both layers empty
c, e = char0_layer(8, 6)
S, mx = norm_spectrum(8, 6)
assert (c, e, S, mx) == (0, 0, [], 1), (c, e, S, mx)
print("(8,4): char-0 empty, S = {}, max norm 1 - clean at EVERY prime  [OK]")

# (8,2): pure char-0 layer
c, e = char0_layer(8, 4)
S, mx = norm_spectrum(8, 4)
assert (c, e, S) == (10, 9, []), (c, e, S)
print(f"(8,2): char-0 = 10 subsets / 9 e1-values, S = {{}} (max norm {mx})  [OK]")


def subgroup(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            elems.add(x)
        if len(elems) == p - 1:
            gen = pow(g, (p - 1) // n, p)
            return sorted(set(pow(gen, i, p) for i in range(n)))


for p in (17, 41, 73, 89, 97, 113, 233, 1009):
    H = subgroup(p, 8)
    lams, cnt = set(), 0
    for A in combinations(H, 4):
        s1 = sum(A) % p
        s2 = sum(x * x % p for x in A) % p
        if (s1 * s1 - s2) % p == 0:
            cnt += 1
            lams.add((-s1) % p)
    assert (cnt, len(lams)) == (10, 9), (p, cnt, len(lams))
print("(8,2) per-prime: #qual = 10, census = 9 at all 8 primes tested  [OK]")
print("O143 two-layer law verdicts reproduced")
