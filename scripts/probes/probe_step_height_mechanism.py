"""Mechanism: why does repCount(c) >= 3 only happen for SMALL primes (p < ~n^3)?

r(c) >= 2 means c = g1+g2 = g3+g4 with {g1,g2} != {g3,g4}, g_i in mu_n.
That is a GENUINE 4-term relation g1 + g2 - g3 - g4 = 0 among n-th roots of unity.

Over CHAR 0 (complex), do genuine (non-swap) such relations exist among mu_n = n-th roots of unity?
If NOT, then in char 0 r(c) <= 2 always (the char-0 Sidon-mod-swap fact), and the F_p violations are
EXACTLY p dividing some fixed nonzero integer (the resultant/height) determined by the relation.

We test the char-0 side: enumerate 4-tuples of n-th roots of unity with g1+g2 = g3+g4 over C.
A non-swap solution = a genuine vanishing 4-term sum of signed roots of unity.
"""
import cmath


def roots_of_unity(n):
    return [cmath.exp(2j * cmath.pi * k / n) for k in range(n)]


for n in (4, 8, 16, 32):
    ru = roots_of_unity(n)
    genuine = 0
    swaps = 0
    examples = []
    for i1 in range(n):
        for i2 in range(n):
            s = ru[i1] + ru[i2]
            for i3 in range(n):
                for i4 in range(n):
                    if abs(ru[i3] + ru[i4] - s) < 1e-9:
                        if {i1, i2} == {i3, i4}:
                            swaps += 1
                        else:
                            genuine += 1
                            if len(examples) < 5 and (i1, i2) < (i3, i4):
                                examples.append((i1, i2, i3, i4))
    print(f"n={n:2d}: char-0 NON-swap g1+g2=g3+g4 = {genuine}  (swaps={swaps})  ex={examples[:5]}")
