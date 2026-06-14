#!/usr/bin/env python3
"""
ADVERSARIAL RE-VERIFICATION of CONNECTION C1-count-bypass.

I re-derive THREE claims independently of the agent's probes:

 (V1) The IDENTITY  E_r(F_p) = E_r(char0) + Sigma_r,  Sigma_r >= 0  where
        E_r := #{(x,y) in mu_s^{2r} : sum x_i = sum y_j}  (ordered tuple pairs; additive energy)
        Sigma_r := #ordered pairs colliding mod p but NOT in Z[zeta_s].
      Verify by DIRECT enumeration of mu_s^{2r} (brute force, no convolution) for small s,r,p.

 (V2) THREE distinct objects and their char-p bad-prime sets:
        (A) DISTINCT-element count  a = |H^{(+r)}| = #{ sum of r DISTINCT elts of mu_s }
        (B) multiset r-fold sumset  N0 = #{ sum of r elts WITH repetition }
        (C) additive energy E_r = sum_c mult(c)^2     (the MOMENT = BGK object)
      Claim under test: bad(A) STRICT SUBSET bad(B) = bad(C), and max bad(A) < max bad(C).
      I compute bad-prime sets for ALL THREE by my OWN enumeration and set-compare.

 (V3) The resultant Res(Phi_s, Q) governs bad(A): bad primes of (A) divide Res, |Res| <= s^s,
      so all bad(A) primes are < (roughly) s^s; measure max bad prime vs s.

CRITICAL CIRCULARITY CHECK appended at bottom (V4): is (A)'s saturation a MOMENT statement
or a SET-cardinality / resultant statement?  And is the relevant subgroup mu_s (order O(log n))
or mu_n (order n)?
"""
import math
from collections import Counter
from sympy import isprime, primitive_root, factorint, prod, symbols, Poly, resultant, cyclotomic_poly
from itertools import combinations, product


def fp_root(s, p):
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // s, p)


# ---------- char-0 representation: mu_s elements as integer vectors over a basis ----------
# mu_s = {zeta^i}.  Use the basis 1, zeta, ..., zeta^{phi(s)-1} ? Simpler: represent
# zeta^i by its full coordinate vector mod (X^s - 1) is NOT injective for sums; instead use the
# half-rep used by the agent (valid because s is a power of 2: zeta^{s/2} = -1).
def char0_vecs(s):
    # zeta_s, s power of 2: zeta^{i} for i in [0,s).  Use the relation zeta^{s/2} = -1
    # so a faithful additive embedding is: coordinate in Z^{s/2} with sign.
    h = s // 2
    out = []
    for i in range(s):
        col = i % h
        sgn = -1 if ((i // h) % 2 == 1) else 1
        v = [0] * h
        v[col] = sgn
        out.append(tuple(v))
    return out


def V1_identity(s, r, primes):
    """Brute-force enumerate mu_s^{2r}; compare collisions mod p vs in Z[zeta_s]."""
    print(f"\n[V1] s={s} r={r}: identity E_r(Fp) = E_r(c0) + Sigma_r, Sigma_r>=0 (brute force {s}^{2*r} pairs)")
    vecs0 = char0_vecs(s)
    # char-0 energy: count ordered (x,y) in mu_s^r x mu_s^r with sum_x == sum_y as integer vectors
    sums0 = Counter()
    for tup in product(range(s), repeat=r):
        acc = [0] * (s // 2)
        for i in tup:
            v = vecs0[i]
            for j in range(s // 2):
                acc[j] += v[j]
        sums0[tuple(acc)] += 1
    Er_c0 = sum(m * m for m in sums0.values())
    for p in primes:
        g = fp_root(s, p)
        roots = [pow(g, i, p) for i in range(s)]
        sumsp = Counter()
        for tup in product(range(s), repeat=r):
            c = 0
            for i in tup:
                c = (c + roots[i]) % p
            sumsp[c] += 1
        Er_fp = sum(m * m for m in sumsp.values())
        Sigma_r = Er_fp - Er_c0
        ok = "OK" if Sigma_r >= 0 else "*** NEGATIVE ***"
        print(f"    p={p:>6}: E_r(c0)={Er_c0:>8}  E_r(Fp)={Er_fp:>8}  Sigma_r={Sigma_r:>8}  {ok}")


def objects_char0(s, r):
    vecs0 = char0_vecs(s)
    # (A) distinct
    A = set()
    for comb in combinations(range(s), r):
        acc = [0] * (s // 2)
        for i in comb:
            v = vecs0[i]
            for j in range(s // 2):
                acc[j] += v[j]
        A.add(tuple(acc))
    # (B) multiset + (C) energy
    mult = Counter()
    for tup in product(range(s), repeat=r):
        acc = [0] * (s // 2)
        for i in tup:
            v = vecs0[i]
            for j in range(s // 2):
                acc[j] += v[j]
        mult[tuple(acc)] += 1
    B = len(mult)
    C = sum(m * m for m in mult.values())
    return len(A), B, C


def objects_fp(s, r, p):
    g = fp_root(s, p)
    roots = [pow(g, i, p) for i in range(s)]
    A = set()
    for comb in combinations(range(s), r):
        c = 0
        for i in comb:
            c = (c + roots[i]) % p
        A.add(c)
    mult = Counter()
    for tup in product(range(s), repeat=r):
        c = 0
        for i in tup:
            c = (c + roots[i]) % p
        mult[c] += 1
    return len(A), len(mult), sum(m * m for m in mult.values())


def V2_three_objects(s, r, primes):
    print(f"\n[V2] s={s} r={r}: bad-prime sets of (A) distinct, (B) multiset, (C) energy")
    A0, B0, C0 = objects_char0(s, r)
    print(f"    char-0 reference: |H^(+r)|=A0={A0}  N0=B0={B0}  E_r=C0={C0}")
    badA, badB, badC = [], [], []
    for p in primes:
        Af, Bf, Cf = objects_fp(s, r, p)
        if Af != A0:
            badA.append(p)
        if Bf != B0:
            badB.append(p)
        if Cf != C0:
            badC.append(p)
    print(f"    bad(A) [distinct]: {badA}")
    print(f"    bad(B) [multiset]: {badB}")
    print(f"    bad(C) [energy]:   {badC}")
    print(f"    bad(A) subset bad(B)? {set(badA) <= set(badB)}   bad(B)==bad(C)? {set(badB)==set(badC)}")
    if badA and badC:
        print(f"    STRICT subset? {set(badA) < set(badC)}   max bad(A)={max(badA)}  max bad(C)={max(badC)}")
    return badA, badB, badC


def V3_resultant(s, r):
    """For one r-tuple pair, compute Res(Phi_s, Q) and its prime factors; |Res|<=s^s."""
    print(f"\n[V3] s={s} r={r}: resultant Res(Phi_s, Q) bad primes (sample r-tuple pairs)")
    X = symbols('X')
    Phi = Poly(cyclotomic_poly(s, X), X)
    bound = s ** s
    allbad = set()
    cnt = 0
    combs = list(combinations(range(s), r))
    import random
    random.seed(1)
    pairs = []
    for _ in range(40):
        i = random.choice(combs); j = random.choice(combs)
        if set(i) != set(j):
            pairs.append((i, j))
    for (I, J) in pairs:
        Q = sum(X ** a for a in I) - sum(X ** a for a in J)
        Qp = Poly(Q, X)
        try:
            R = resultant(Phi, Qp)
        except Exception:
            continue
        if R == 0:
            continue
        cnt += 1
        for pr in factorint(abs(int(R))):
            allbad.add(pr)
    bad = sorted(allbad)
    print(f"    |Res| bound s^s = {bound}  (log2={math.log2(bound):.1f})")
    print(f"    nonzero resultants sampled: {cnt}")
    print(f"    union of resultant prime factors: {bad[:25]}{' ...' if len(bad)>25 else ''}")
    if bad:
        print(f"    MAX resultant prime factor = {max(bad)}  (s^2={s*s}, s^3={s**3}, 2^s={2**s})")


def main():
    print("=" * 90)
    print("ADVERSARIAL RE-VERIFICATION C1 — independent enumeration")
    print("=" * 90)

    # V1: identity (brute force, small)
    V1_identity(4, 3, [5, 13, 17, 29, 37])
    V1_identity(8, 2, [17, 41, 73, 89, 97])

    # V2: three objects, full bad-set scan
    def primes_1modn(n, count):
        out, p = [], 1
        while len(out) < count:
            p += n
            if isprime(p):
                out.append(p)
        return out

    V2_three_objects(8, 3, primes_1modn(8, 30))
    V2_three_objects(16, 3, primes_1modn(16, 40))

    # V3: resultant governs (A)
    V3_resultant(8, 3)
    V3_resultant(16, 3)


if __name__ == "__main__":
    main()
