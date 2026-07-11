"""Exclusion of fiber patterns (b,r) != (s/2-1,3), 2b+r = s+1, general s.
Same antipodal-balance law: non-B terms = C(r,2) products + r O-terms + L;
B placed by the forced/free-axis rule.  r = 1 is the witness layer a priori.
Claim: r >= 5 has ZERO balanced configurations.
"""
from itertools import combinations
from math import comb
import sys

def sweep(s, r):
    n = 2 * s
    A = s // 2
    b = (s + 1 - r) // 2
    Lexp = (3 * s // 2) % n
    pairs = list(combinations(range(r), 2))
    total = 0
    for O in combinations(range(s), r):
        for m in range(1 << (r - 1)):                 # d_1 = 0 (negation rep)
            a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
            cnt = [0] * n
            for (i, j) in pairs:
                cnt[(a[i] + a[j]) % n] += 1
            for o in O:
                cnt[(2 * o) % n] += 1
            cnt[Lexp] += 1
            ok = True
            for mm in range(1, s, 2):
                if cnt[mm] != cnt[mm + s]:
                    ok = False
                    break
            if not ok:
                continue
            Oset = set(O)
            h = v = 0
            for c in range(A):
                d = cnt[2 * c] - cnt[(2 * c + s) % n]
                if d < -1 or d > 1:
                    ok = False
                    break
                if d == -1:
                    if c in Oset:
                        ok = False
                        break
                    h += 1
                elif d == 1:
                    if (c + A) in Oset:
                        ok = False
                        break
                    h += 1
                else:
                    if c not in Oset and (c + A) not in Oset:
                        v += 1
            if not ok:
                continue
            if h <= b and (b - h) % 2 == 0 and (b - h) // 2 <= v:
                total += comb(v, (b - h) // 2)
    return total

if __name__ == '__main__':
    s = int(sys.argv[1])
    rs = [int(x) for x in sys.argv[2:]] or list(range(3, min(s, s + 1) + 1, 2))
    for r in rs:
        t = sweep(s, r)
        print(f"s={s} pattern r={r:2d} (b={(s+1-r)//2}): balanced configs = {t}")
