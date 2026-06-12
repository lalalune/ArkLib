#!/usr/bin/env python3
"""Machine check of Lemma P (r=5 parity purity, proof by derangement sums):
for every mixed-parity O (p odd fibers, p in 1..4) and every sign class,
the odd-exponent sub-multiset {a_i+a_j : o_i+o_j odd} is NOT antipodally
balanced. The proof says: a perfect antipodal matching would force
q*(a_x - a_y) = s (mod 2s) with q in {3} (p=2,3) or pair-sharing (p=1,4),
impossible for distinct fibers. Checked exhaustively at s=16 and s=32."""
from itertools import combinations

def check(s):
    n = 2 * s
    viol = 0; tested = 0
    for O in combinations(range(s), 5):
        p = sum(o & 1 for o in O)
        if p in (0, 5): continue
        for m in range(16):
            a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, 5)]
            cnt = [0] * n
            for i in range(5):
                for j in range(i + 1, 5):
                    if (O[i] + O[j]) & 1:
                        cnt[(a[i] + a[j]) % n] += 1
            tested += 1
            if all(cnt[t] == cnt[t + s] for t in range(1, s, 2)):
                viol += 1
    return tested, viol

for s in (16, 32):
    t, v = check(s)
    print(f"s={s}: mixed-parity sign-classes tested {t}, odd-balanced found {v}")
    assert v == 0
print("LEMMA P MACHINE CHECK PASSES (s=16, s=32)")
