"""DERIVER STEP 4: exclusion of all fiber patterns (b,r) != (7,3), 2b+r = 17.

Same antipodal-balance law, general r: non-B terms = C(r,2) products + r O-terms + L;
B (b = (17-r)/2 full fibers) placed by the same forced/free-axis rule.
  r = 1  (b=8): excluded a priori: xi = -x1, so e = Prod_{9 fibers}(X^2-z): agree-18.
  r = 3  (b=7): must give 672 (validation).
  r >= 5: claim 0 balanced configurations AT ALL (so no agree-17 elements, regardless
          of the xi side condition).
"""
from itertools import combinations
from math import comb

def sweep(r):
    b = (17 - r) // 2
    total = 0
    pairs = list(combinations(range(r), 2))
    for O in combinations(range(16), r):
        for m in range(1 << (r - 1)):           # delta_1 = 0
            a = [O[0]] + [O[i] + 16 * ((m >> (i - 1)) & 1) for i in range(1, r)]
            n = [0] * 32
            for (i, j) in pairs:
                n[(a[i] + a[j]) % 32] += 1
            for o in O:
                n[(2 * o) % 32] += 1
            n[24] += 1
            ok = True
            for mm in range(1, 16, 2):
                if n[mm] != n[mm + 16]:
                    ok = False
                    break
            if not ok:
                continue
            Oset = set(O)
            h = 0
            v = 0
            for c in range(8):
                d = n[2 * c] - n[(2 * c + 16) % 32]
                if d < -1 or d > 1:
                    ok = False
                    break
                if d == -1:
                    if c in Oset:
                        ok = False
                        break
                    h += 1
                elif d == 1:
                    if (c + 8) in Oset:
                        ok = False
                        break
                    h += 1
                else:
                    if c not in Oset and (c + 8) not in Oset:
                        v += 1
            if not ok:
                continue
            if h <= b and (b - h) % 2 == 0 and (b - h) // 2 <= v:
                total += comb(v, (b - h) // 2)
    return total

print("pattern (b,r) balanced-configuration counts (sigma-classes x B-completions):")
for r in (3, 5, 7, 9, 11, 13, 15):
    t = sweep(r)
    print(f"  r = {r:2d} (b = {(17-r)//2}): {t}")
    if r == 3:
        assert t == 672
    else:
        assert t == 0, f"r={r} has {t} balanced configs - xi analysis needed!"
print("ALL OTHER PATTERNS EXCLUDED: the agree-17 layer is exactly the (7,3) family.")
