# O142: the norm-divisibility spectrum at rate 1/4 - and a CORRECTION to O139's reading.
#
# O139 measured the (16,4) depth-1 row (a = k+2 = 6, delta = .625) as nonzero at all four
# scanned primes {17,97,113,193} and read it as "field-dependent, ~n at large p". O141's
# norm principle says otherwise, and this probe confirms it:
#
#  (1) the char-0 layer at (16,4) depth 1 is EMPTY (no 6-subset of mu_16 has e2 = 0 in
#      Z[zeta_16]) - same as rate 1/2;
#  (2) the complete qualifying-prime set is
#        S(16,4) = {17, 97, 113, 193, 241, 257, 337, 353, 433, 593, 673, 881, 1201,
#                   1601, 2593, 2833, 4049}   (max |N(e2(A))| = 4097 = 2^12 + 1);
#      O139's four scanned primes ALL lie in S - the "always nonzero" reading was a
#      scan-range coincidence;
#  (3) per-prime validation across ALL primes = 1 mod 16 up to 2161: depth-1 census
#      nonzero <=> p in S(16,4), zero mismatches. For p > 4049: clean forever.
#
# So at BOTH production rates measured, the candidate-extremal family's window interior
# strip below capacity - 1/n is bad only on an explicit finite set of primes, with Fermat-
# flavored maxima (4097 = 2^12+1 at rate 1/4; 18433 at rate 1/2): the mid-window question
# for this family is purely the arithmetic of cyclotomic norms of subset power sums.
from itertools import combinations
import cmath

N16, K = 16, 4
A_DEPTH1 = K + 2  # = 6


def zpow(j):
    j %= 16
    v = [0] * 8
    if j < 8:
        v[j] = 1
    else:
        v[j - 8] = -1
    return tuple(v)


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def mul(u, v):
    out = [0] * 15
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                if b:
                    out[i + j] += a * b
    for i in range(14, 7, -1):
        out[i - 8] -= out[i]
        out[i] = 0
    return tuple(out[:8])


ZERO = tuple([0] * 8)

char0 = 0
for A in combinations(range(16), A_DEPTH1):
    s1, s2 = ZERO, ZERO
    for j in A:
        s1 = add(s1, zpow(j))
        s2 = add(s2, zpow(2 * j))
    if tuple(a - b for a, b in zip(mul(s1, s1), s2)) == ZERO:
        char0 += 1
assert char0 == 0, char0
print("char-0 depth-1 census at (16,4): 0  [OK]")

ROOTS = [cmath.exp(2j * cmath.pi * j / 16) for j in range(16)]
UNITS = [t for t in range(16) if t % 2 == 1]


def e2c(A, t):
    s1 = sum(ROOTS[(t * j) % 16] for j in A)
    s2 = sum(ROOTS[(2 * t * j) % 16] for j in A)
    return (s1 * s1 - s2) / 2


vals = set()
for A in combinations(range(16), A_DEPTH1):
    prod = 1.0 + 0j
    for t in UNITS:
        prod *= e2c(A, t)
    n = round(prod.real)
    assert abs(prod.imag) < 1e-5 and abs(prod.real - n) < 2e-4, (A, prod)
    if n:
        vals.add(abs(n))


def primes_of(n):
    fs, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return fs


spec = set()
for v in vals:
    spec |= primes_of(v)
S = sorted(p for p in spec if p % 16 == 1)
assert S == [17, 97, 113, 193, 241, 257, 337, 353, 433, 593, 673, 881, 1201,
             1601, 2593, 2833, 4049], S
assert max(vals) == 4097
print(f"S(16,4) = {S}, max norm 4097  [OK]")


def subgroup(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            elems.add(x)
        if len(elems) == p - 1:
            gen = pow(g, (p - 1) // n, p)
            return sorted(set(pow(gen, i, p) for i in range(n)))


primes = [p for p in range(17, 2200) if (p - 1) % 16 == 0
          and all(p % d for d in range(2, int(p ** 0.5) + 1))]
for p in primes:
    H = subgroup(p, 16)
    cnt = 0
    for A in combinations(H, A_DEPTH1):
        s1 = sum(A) % p
        s2 = sum(a * a % p for a in A) % p
        # e2 = (e1^2 - p2)/2
        if (s1 * s1 - s2) % p == 0:
            cnt += 1
    assert (cnt > 0) == (p in S), (p, cnt)
print(f"depth-1 nonzero <=> p in S(16,4), verified for all {len(primes)} primes <= 2161  [OK]")
print("O142 verdicts reproduced")
