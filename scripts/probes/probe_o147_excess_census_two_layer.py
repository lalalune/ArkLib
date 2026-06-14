# O147: the two-layer law EXTENDS to the excess census, and the CA/MCA gap localizes on
# coset witness sets - the take-over family's flat-n numerator explained.
#
# Setting (the take-over instance of the death-radius comment): stack (X^9, X^8) over
# mu_16 in F_p, k = 4, agreement a = 7 (one below the adjacent death rung), excess
# s - a = 2. Qualifying condition for a witness 7-subset A and scalar gamma:
# X^9 + gamma X^8 - c vanishes on A for some deg-<4 c, i.e. the band system
#   p_{j-2} + g1 p_{j-1} + g0 p_j = 0  (j = 4..7),  gamma = p_6 + g1,
# where P_A = prod_{alpha in A}(X - zeta^alpha) = sum p_i X^i and g = X^2 + g1 X + g0.
#
# Verdicts (exact; char-0 side in Q(zeta_16) via fraction arithmetic mod Phi_16,
# mod-p side at p = 97):
#  (1) SUBSET census is pure layer-1: 464 qualifying 7-subsets in char 0 AND mod 97.
#  (2) Of these, exactly 16 carry a full gamma-LINE (band system rank 1): they are
#      precisely the C(8,7)x2 = 16 seven-subsets of the two parity classes (the index-2
#      subgroup {even exponents} and its coset). On a parity-class witness X^8 = +-1 and
#      X^9 = +-X - both rows are low-degree codewords there, so the stack is JOINTLY
#      EXPLAINABLE on these witnesses and the MCA event does NOT fire: the entire
#      gamma-line layer is CA-bad but MCA-invisible. The CA/MCA gap of the excess census
#      is exactly the coset-witness layer.
#  (3) The remaining 448 subsets pin gamma, with exactly 16 = n distinct pinned values,
#      field-independent (char-0 values reduced mod p) - THE FLAT-n LAW of the take-over
#      family is the pinned part of the char-0 band locus. Matches the measured
#      "16 bad scalars at both p = 97, 193" of the take-over comment.
#
# Consequence: census(MCA, excess row) = pinned-gamma char-0 census (+ finite-spectrum
# surplus at exceptional primes, by the O141 norm principle applied to the band minors);
# the gamma-line/coset layer must be subtracted - any future excess-census ledger entry
# needs the explainability filter, not just the band system.
from itertools import combinations
from fractions import Fraction

H = 8


def zp(j):
    j %= 16
    v = [Fraction(0)] * H
    if j < 8:
        v[j] = Fraction(1)
    else:
        v[j - 8] = Fraction(-1)
    return v


def vadd(u, v):
    return [a + b for a, b in zip(u, v)]


def vsub(u, v):
    return [a - b for a, b in zip(u, v)]


def vmul(u, v):
    out = [Fraction(0)] * (2 * H - 1)
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                if b:
                    out[i + j] += a * b
    for i in range(2 * H - 2, H - 1, -1):
        out[i - H] -= out[i]
        out[i] = Fraction(0)
    return out[:H]


def vneg(u):
    return [-a for a in u]


def is_zero(u):
    return all(a == 0 for a in u)


ZERO = [Fraction(0)] * H
ONE = zp(0)


def vinv(u):
    cols = []
    for j in range(H):
        xj = [Fraction(0)] * H
        xj[j] = Fraction(1)
        cols.append(vmul(u, xj))
    M = [[cols[j][i] for j in range(H)] for i in range(H)]
    b = [Fraction(1)] + [Fraction(0)] * (H - 1)
    for col in range(H):
        piv = next((r for r in range(col, H) if M[r][col] != 0), None)
        assert piv is not None
        M[col], M[piv] = M[piv], M[col]
        b[col], b[piv] = b[piv], b[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        b[col] = b[col] / pv
        for r in range(H):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
                b[r] = b[r] - f * b[col]
    return b


def polyA(A):
    coeffs = [ONE[:]]
    for alpha in A:
        za = zp(alpha)
        new = [ZERO[:] for _ in range(len(coeffs) + 1)]
        for i, c in enumerate(coeffs):
            new[i + 1] = vadd(new[i + 1], c)
            new[i] = vsub(new[i], vmul(za, c))
        coeffs = new
    return coeffs


# ---- char-0 side ----
pinned_gammas = set()
nline = npin = 0
line_subsets = []
for A in combinations(range(16), 7):
    P = polyA(A)

    def p(i):
        return P[i] if 0 <= i < len(P) else ZERO

    R = [(p(j - 1), p(j), vneg(p(j - 2))) for j in range(4, 8)]
    piv = next((i for i, r in enumerate(R) if not is_zero(r[0])), None)
    assert piv is not None
    inv = vinv(R[piv][0])
    arow = vmul(inv, R[piv][1])
    brow = vmul(inv, R[piv][2])
    red = []
    for i, r in enumerate(R):
        if i == piv:
            continue
        red.append((vsub(r[1], vmul(r[0], arow)), vsub(r[2], vmul(r[0], brow))))
    piv2 = next((i for i, (c1, _) in enumerate(red) if not is_zero(c1)), None)
    if piv2 is None:
        if all(is_zero(c2) for _, c2 in red):
            nline += 1
            line_subsets.append(A)
        continue
    inv2 = vinv(red[piv2][0])
    g0 = vmul(inv2, red[piv2][1])
    if not all(is_zero(vsub(c2, vmul(c1, g0))) for c1, c2 in red):
        continue
    g1 = vsub(brow, vmul(arow, g0))
    npin += 1
    pinned_gammas.add(tuple(vadd(p(6), g1)))

assert (nline, npin, len(pinned_gammas)) == (16, 448, 16), (nline, npin, len(pinned_gammas))
print(f"char-0: 16 gamma-line subsets + 448 pinned subsets, 16 distinct pinned gammas  [OK]")

evens = set(range(0, 16, 2))
odds = set(range(1, 16, 2))
assert all(set(A) <= evens or set(A) <= odds for A in line_subsets)
print("gamma-line subsets = exactly the 16 parity-class 7-subsets (jointly explainable:")
print("  X^8 = +-1 and X^9 = +-X on a parity class => MCA event cannot fire there)  [OK]")

# ---- mod-97 side ----
p = 97


def find_gen():
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            elems.add(x)
        if len(elems) == p - 1:
            return pow(g, (p - 1) // 16, p)


gen = find_gen()
modpin = set()
mline = mpin = 0
for A in combinations(range(16), 7):
    pts = [pow(gen, i, p) for i in A]
    coeffs = [1]
    for a in pts:
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i + 1] = (new[i + 1] + c) % p
            new[i] = (new[i] - a * c) % p
        coeffs = new

    def pc(i):
        return coeffs[i] if 0 <= i < len(coeffs) else 0

    gs = set()
    for g1 in range(p):
        for g0 in range(p):
            if all((pc(j - 2) + g1 * pc(j - 1) + g0 * pc(j)) % p == 0 for j in range(4, 8)):
                gs.add((pc(6) + g1) % p)
                if len(gs) > 20:
                    break
        if len(gs) > 20:
            break
    if not gs:
        continue
    if len(gs) > 20:
        mline += 1
    else:
        mpin += 1
        modpin |= gs
assert (mline, mpin, len(modpin)) == (16, 448, 16), (mline, mpin, len(modpin))
print(f"mod 97: 16 line + 448 pinned subsets, 16 distinct pinned gammas = char-0 counts")
print("  (pure layer-1 at p = 97; flat-n numerator = the pinned char-0 census)  [OK]")
print("O147 verdicts reproduced")
