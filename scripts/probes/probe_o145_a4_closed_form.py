# O145: closed form + structure theorem for the a = 4 char-0 vanishing locus:
#
#   N4(n) = n(n-3)/4,  and every solution contains an antipodal pair.
#
# Derivation: a 4-subset with an antipodal pair is A = {x, -x} u {s, t}; cross terms
# vanish (e1({x,-x}) = 0), so e2(A) = -x^2 + st = 0 iff st = x^2. Count: n/2 antipodal
# classes x, times (n-2)/2 unordered admissible {s,t} (s ranges over mu_n \ {+-x},
# t = x^2/s), minus the double-counted two-pair solutions {+-x, +-ix} (n/4 of them):
#   N4 = (n/2)(n-2)/2 - n/4 = n(n-3)/4.
# The count MATCHES the measured census exactly at n = 8, 16, 32 (10/52/232) and the
# blind n = 64 forecast (976) verified by exhaustive scan - which simultaneously proves
# (at these scales) that NO antipodal-free solutions exist (also checked directly at
# n = 64: zero solutions without an antipodal pair).
#
# Status of the a = 8 layer: (16,8) has 70 = C(8,4) solutions - closed form OPEN (the
# pure 4-antipodal-pair ansatz gives only 6; the coincidence 70 = C(8,4) is unexplained).
from itertools import combinations


def char0_solutions(n, a):
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

    ZERO = tuple([0] * half)
    sols = []
    for A in combinations(range(n), a):
        s1, s2 = ZERO, ZERO
        for j in A:
            s1 = add(s1, zp(j))
            s2 = add(s2, zp(2 * j))
        if tuple(x - y for x, y in zip(mul(s1, s1), s2)) == ZERO:
            sols.append(A)
    return sols


for n in (8, 16, 32, 64):
    sols = char0_solutions(n, 4)
    pred = n * (n - 3) // 4
    assert len(sols) == pred, (n, len(sols), pred)
    no_pair = [A for A in sols if not any((j + n // 2) % n in set(A) for j in A)]
    assert no_pair == [], (n, no_pair[:3])
    print(f"n={n}: N4 = {len(sols)} = n(n-3)/4  [OK]; antipodal-free solutions: 0  [OK]")
print("O145 verdicts reproduced (n=64 was a blind forecast, confirmed)")
