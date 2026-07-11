"""Probe: ring-hom / Frobenius naturality of the divided-difference power.

  sigma(DD_s(v)(b)) =?= DD_s(sigma . v)(b)

DD_s(v)(b) = sum_{i in s} v_i^b * prod_{j != i}(v_i - v_j)^{-1}.

We test over F_{p^2} with sigma = Frobenius x -> x^p (the nontrivial Galois
generator of F_{p^2}/F_p = conjugation), on distinct node sets (the genuine
RS-node regime: v injective on s). This is the naturality lemma Shaw flagged
as the lost _SpecS3 substrate worth re-deriving.
"""
import random


def make_field(p):
    # monic irreducible t^2 - c with c a quadratic non-residue
    for c in range(2, p):
        if pow(c, (p - 1) // 2, p) == p - 1:
            return c
    return None


def fp2_mul(a, b, c, p):
    a0, a1 = a
    b0, b1 = b
    lo = (a0 * b0 + a1 * b1 * c) % p
    hi = (a0 * b1 + a1 * b0) % p
    return (lo, hi)


def fp2_pow(a, e, c, p):
    r = (1, 0)
    base = a
    while e > 0:
        if e & 1:
            r = fp2_mul(r, base, c, p)
        base = fp2_mul(base, base, c, p)
        e >>= 1
    return r


def fp2_inv(a, c, p):
    return fp2_pow(a, p * p - 2, c, p)


def fp2_sub(a, b, p):
    return ((a[0] - b[0]) % p, (a[1] - b[1]) % p)


def fp2_add(a, b, p):
    return ((a[0] + b[0]) % p, (a[1] + b[1]) % p)


def frob(a, p):
    # x -> x^p on F_{p^2} = conjugation (a0,a1) -> (a0,-a1)
    return (a[0] % p, (-a[1]) % p)


def dd_pow_fp2(vs, b, c, p):
    tot = (0, 0)
    for i in range(len(vs)):
        num = fp2_pow(vs[i], b, c, p)
        den = (1, 0)
        for j in range(len(vs)):
            if j == i:
                continue
            den = fp2_mul(den, fp2_sub(vs[i], vs[j], p), c, p)
        tot = fp2_add(tot, fp2_mul(num, fp2_inv(den, c, p), c, p), p)
    return tot


def main():
    random.seed(7)
    fails = 0
    tests = 0
    for _ in range(4000):
        p = random.choice([101, 103, 107, 1009, 2003, 10007, 100003])
        c = make_field(p)
        if c is None:
            continue
        k = random.randint(2, 5)
        nodes = set()
        while len(nodes) < k:
            nodes.add((random.randrange(p), random.randrange(p)))
        vs = list(nodes)
        b = random.randint(0, 12)
        lhs = frob(dd_pow_fp2(vs, b, c, p), p)
        rhs = dd_pow_fp2([frob(v, p) for v in vs], b, c, p)
        tests += 1
        if lhs != rhs:
            fails += 1
            if fails <= 5:
                print("FAIL", p, b, vs, lhs, rhs)
    print("naturality under Frobenius on F_p^2:", fails, "fails /", tests, "tests")


if __name__ == "__main__":
    main()
