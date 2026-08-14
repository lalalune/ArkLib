# O144: THE PARITY LAW of the char-0 layer - the depth-1 vanishing locus is governed by
# |A| mod 4, with a one-line F_2 proof; production dimensions are char-0-clean UNIFORMLY.
#
# Data (exact, this probe + the companion C enumerator for (32,10)):
#   a = 4  (pairs even):  n=8: 10 solutions, n=16: 52, n=32: 232   - NONZERO
#   a = 8  (pairs even):  n=16: 70                                  - NONZERO
#   a = 6  (pairs odd):   n=16: 0                                   - EMPTY
#   a = 10 (pairs odd):   n=16: 0 (O141), n=32: 0 (C scan of all 64,512,240 subsets)
#
# THE LAW + PROOF: the ring map Z[zeta_{2^m}] -> F_2 sending zeta -> 1 (well-defined since
# Phi_{2^m}(1) = 2) sends e2(A) to C(|A|,2) mod 2. So e2(A) = 0 forces C(a,2) even, i.e.
# a = 0 or 1 (mod 4). For a = 2 (mod 4) - which is exactly the depth-1 row a = k+2 at
# every PRODUCTION dimension k = 0 (mod 4), in particular all k = 2^j, j >= 2 - the
# char-0 layer is EMPTY at every smooth scale n = 2^m, uniformly, with no enumeration.
#
# Combined with the O141 norm threshold (formal: WindowTwoLayerThreshold.lean), this
# yields: at production dimensions the adjacent-pair family's depth-1 mid-window row is
# clean at every prime above an explicit threshold, for every smooth n - the first
# uniform-in-n formal cleanliness statement inside the window. The k = 2 (mod 4)
# dimensions (e.g. (8,2)) are the only ones with a persistent field-independent layer.
from itertools import combinations


def char0_count(n, a):
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
    cnt = 0
    for A in combinations(range(n), a):
        s1, s2 = ZERO, ZERO
        for j in A:
            s1 = add(s1, zp(j))
            s2 = add(s2, zp(2 * j))
        if tuple(x - y for x, y in zip(mul(s1, s1), s2)) == ZERO:
            cnt += 1
    return cnt


expected = {(8, 4): 10, (16, 4): 52, (32, 4): 232, (16, 8): 70,
            (16, 6): 0, (16, 10): 0, (8, 6): 0}
for (n, a), want in sorted(expected.items()):
    got = char0_count(n, a)
    assert got == want, (n, a, got, want)
    parity = "even" if (a * (a - 1) // 2) % 2 == 0 else "odd"
    print(f"n={n} a={a} (C(a,2) {parity}): char0 = {got}  [OK]")

# the law: empty whenever C(a,2) is odd (a = 2,3 mod 4)
for (n, a), want in expected.items():
    if (a * (a - 1) // 2) % 2 == 1:
        assert want == 0
print("parity law verified on all measured instances; (32,10)=0 by the companion C scan")
print("O144 verdicts reproduced")
