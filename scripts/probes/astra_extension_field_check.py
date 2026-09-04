#!/usr/bin/env python3
"""Independent direct MCA census over F9 and F25, using only the stdlib.

Every scalar, every affine codeword, and all 64 monomial pairs are enumerated.
No cyclotomic determinant, polynomial remainder, or candidate-label routine is
used. This is an error-detection check for the separate field-uniform certificate,
not a proof about arbitrary field sizes or production parameters.
"""

from itertools import product


def direct_extension_profile(p, d):
    """Return the direct event census in F_p[u]/(u^2-d), with d nonsquare.

    Encode a+b*u as a+p*b for canonical integers 0<=a,b<p. Only the
    independently checked prime characteristics 3 and 5 are used here.
    """
    assert p in (3, 5)
    assert pow(d, (p - 1) // 2, p) == p - 1
    q = p * p

    def add(x, y):
        return ((x % p + y % p) % p) + p * ((x // p + y // p) % p)

    def negate(x):
        return (-(x % p)) % p + p * ((-(x // p)) % p)

    def multiply(x, y):
        a, b, c, e = x % p, x // p, y % p, y // p
        return (a * c + d * b * e) % p + p * ((a * e + b * c) % p)

    def power(x, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = multiply(result, x)
            x = multiply(x, x)
            exponent //= 2
        return result

    assert all(power(x, q - 1) == 1 for x in range(1, q))
    g = next(x for x in range(q) if power(x, 4) == negate(1))
    domain = [power(g, i) for i in range(8)]
    assert len(set(domain)) == 8 and power(g, 8) == 1
    words = [tuple(power(x, a) for x in domain) for a in range(8)]
    codewords = [tuple(add(multiply(s, x), t) for x in domain)
                 for s, t in product(range(q), repeat=2)]
    assert len(set(codewords)) == q * q

    def agreement_mask(first, second):
        return sum(1 << i for i in range(8) if first[i] == second[i])

    # A mask is extendable iff at least one of all q^2 affine codewords agrees
    # with the word at every coordinate in that mask. This directly implements
    # the codeword quantifier in pairJointAgreesOn.
    extendable = []
    for word in words:
        masks = [agreement_mask(word, codeword) for codeword in codewords]
        extendable.append({support for support in range(256)
                           if any(support & mask == support for mask in masks)})

    profile = []
    for a, first_word in enumerate(words):
        row = []
        for b, second_word in enumerate(words):
            bad = 0
            for gamma in range(q):
                line = tuple(add(x, multiply(gamma, y))
                             for x, y in zip(first_word, second_word))
                # It suffices to use each affine codeword's full agreement set:
                # a nonjoint subset remains nonjoint when enlarged to this set.
                masks = [agreement_mask(line, codeword) for codeword in codewords]
                if any(support.bit_count() >= 4
                       and not (support in extendable[a] and support in extendable[b])
                       for support in masks):
                    bad += 1
            row.append(bad)
        profile.append(tuple(row))
    return tuple(profile), (g % p, g // p)


def main():
    results = [(p, d, *direct_extension_profile(p, d)) for p, d in ((3, 2), (5, 2))]
    # Expected data is imported only after both independent enumerations finish.
    from astra_order_eight_monomial_certificate import EXPECTED_PROFILE
    for p, d, profile, generator in results:
        assert profile == EXPECTED_PROFILE, (p, profile)
        maximizers = tuple((a, b) for a, b in product(range(8), repeat=2)
                           if profile[a][b] == 9)
        assert maximizers == ((4, 3), (4, 7), (5, 2), (5, 6))
        print(f"F{p*p}=F{p}[u]/(u^2-{d}), g={generator[0]}+{generator[1]}u: "
              f"all64 pairs PASS; max9 at {maximizers}")
    print("PASS: exhaustive scalars and affine codewords in both extension fields")


if __name__ == "__main__":
    main()
