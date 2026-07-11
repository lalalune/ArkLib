"""Confirm: in char 0, every NON-swap relation g1+g2=g3+g4 (g_i n-th roots of unity, n=2^a)
has g1+g2 = 0 (antipodal). I.e. for c != 0, repCount(c) <= 1 (unordered) over C.
Mechanism: g1+g2=g3+g4, {g1,g2}!={g3,g4} -> g1-g3 = g4-g2. For n=2^a roots of unity a
4-term vanishing sum decomposes into antipodal pairs (Mann/Conway-Jones: minimal vanishing
sums of roots of unity of 2-power order are {x,-x}). So the only way is g1=-g2 & g3=-g4 (c=0),
or g1=-g4 & g2=-g3 (also c=0 after sign), i.e. the relation is forced to c=0.
"""
import cmath


def roots_of_unity(n):
    return [cmath.exp(2j * cmath.pi * k / n) for k in range(n)]


for n in (4, 8, 16, 32):
    ru = roots_of_unity(n)
    nonswap_total = 0
    nonswap_c_nonzero = 0
    for i1 in range(n):
        for i2 in range(n):
            s = ru[i1] + ru[i2]
            for i3 in range(n):
                for i4 in range(n):
                    if abs(ru[i3] + ru[i4] - s) < 1e-9 and {i1, i2} != {i3, i4}:
                        nonswap_total += 1
                        if abs(s) > 1e-9:  # c != 0
                            nonswap_c_nonzero += 1
    print(f"n={n:2d}: non-swap total={nonswap_total}, of which c!=0: {nonswap_c_nonzero}  "
          f"==> {'ALL at c=0 (char-0 Sidon for c!=0 CONFIRMED)' if nonswap_c_nonzero==0 else 'SOME at c!=0 (claim FALSE)'}")
