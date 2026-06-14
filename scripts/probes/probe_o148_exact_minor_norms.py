# O148 follow-up: EXACT-INTEGER recomputation of the take-over row's minor-norm
# candidate spectrum (discharging the float-norm caveat of probe_o148_takeover_row_pinned).
#
# The take-over row ((X^9, X^8) @ a = 7 over mu_16) has its char-p surplus layer confined
# to primes dividing a cyclotomic norm of a 3x3 minor of the augmented band matrix
#   rows_j = (c_{j-1}, c_j, -c_{j-2}),  j = 4..8 (4 rows),
# over the NON-degenerate 7-subsets (char-0 rank 3), where c_i are the coefficients of
# the vanishing polynomial prod_{i in A}(X - zeta^i) in Z[zeta_16].
#
# O148 computed the candidate set with float-embedded norms. Here everything is EXACT:
# Z[zeta_16] = Z[X]/(X^8 + 1) with integer vectors; the norm is the product of the eight
# Galois conjugates alpha(X^k), k odd in [1, 16) — a rational integer, computed exactly.
# Output: the exact set of primes p = 1 (mod 16) dividing some nonzero minor norm,
# compared against the O148 float-derived candidate list.
from itertools import combinations

N = 16
HALF = 8  # deg Phi_16 = 8, modulus X^8 + 1


def red(v):
    # reduce an integer coefficient list to length 8 modulo X^8 + 1
    out = [0] * HALF
    for i, c in enumerate(v):
        q, r = divmod(i, HALF)
        out[r] += c if q % 2 == 0 else -c
    return out


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return red(out)


def padd(a, b):
    return [x + y for x, y in zip(a, b)]


def psub(a, b):
    return [x - y for x, y in zip(a, b)]


def zeta_pow(e):
    # zeta^e as a vector in Z[X]/(X^8+1)
    v = [0] * HALF
    e %= N
    if e < HALF:
        v[e] = 1
    else:
        v[e - HALF] = -1
    return v


def conj(a, k):
    # alpha(X) -> alpha(X^k)
    out = [0] * (HALF * k - k + 1) if a else [0]
    out = [0] * ((HALF - 1) * k + 1)
    for i, c in enumerate(a):
        out[i * k] += c
    return red(out)


def norm(a):
    # product of the eight conjugates; result must be a rational integer
    prod = [1] + [0] * (HALF - 1)
    for k in range(1, N, 2):
        prod = pmul(prod, conj(a, k))
    assert all(c == 0 for c in prod[1:]), f"norm not rational: {prod}"
    return prod[0]


def det3(m):
    # 3x3 determinant over the ring
    a, b, c = m[0]
    d, e, f = m[1]
    g, h, i = m[2]
    t1 = pmul(a, psub(pmul(e, i), pmul(f, h)))
    t2 = pmul(b, psub(pmul(d, i), pmul(f, g)))
    t3 = pmul(c, psub(pmul(d, h), pmul(e, g)))
    return padd(psub(t1, t2), t3)


def vanishing_coeffs(A):
    # coefficients (ascending) of prod_{i in A} (X - zeta^i), length 8 each
    coeffs = [[1] + [0] * (HALF - 1)]
    for i in A:
        z = zeta_pow(i)
        new = [[0] * HALF for _ in range(len(coeffs) + 1)]
        for j, c in enumerate(coeffs):
            new[j + 1] = padd(new[j + 1], c)
            new[j] = psub(new[j], pmul(z, c))
        coeffs = new
    return coeffs


def factor(n):
    n = abs(n)
    out = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1
    if n > 1:
        out.add(n)
    return out


ZERO = [0] * HALF
norms = set()
rank3 = rank_lt3 = 0
for A in combinations(range(N), 7):
    cs = vanishing_coeffs(A)

    def pc(i):
        return cs[i] if 0 <= i < len(cs) else ZERO

    rows = [(pc(j - 1), pc(j), [-c for c in pc(j - 2)]) for j in range(4, 8)]
    minors = []
    for triple in combinations(rows, 3):
        d = det3(triple)
        if any(d):
            minors.append(d)
    if minors:
        rank3 += 1
        for d in minors:
            norms.add(norm(d))
    else:
        rank_lt3 += 1

primes = set()
for nm in norms:
    if nm:
        primes |= factor(nm)
cands = sorted(p for p in primes if p % 16 == 1)
print(f"subsets: rank3={rank3} rank<3={rank_lt3} (total {rank3 + rank_lt3})")
print(f"distinct nonzero minor norms: {len([n for n in norms if n])}")
print(f"EXACT candidate primes (p = 1 mod 16): {cands}")
FLOAT_CANDS = [17, 97, 113, 193, 241, 257, 337, 353, 401, 433, 449, 577, 641, 977, 1489, 6833]
extra = sorted(set(cands) - set(FLOAT_CANDS))
missing = sorted(set(FLOAT_CANDS) - set(cands))
print(f"vs float list: extra={extra} missing={missing}")
if not extra:
    print("VERDICT: float candidate set CONFIRMED COMPLETE (no prime was missed); "
          "O148 caveat discharged" + ("" if not missing else
          f" (float list had {len(missing)} spurious entries: {missing})"))
else:
    print("VERDICT: float list INCOMPLETE - rerun the O148 census at the extra primes!")
