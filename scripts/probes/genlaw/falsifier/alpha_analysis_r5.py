"""Bad-alpha census for the SAMPLED r=5 spurious classes (from class-mode
SPUR_B dumps): alpha vector per explicit spurious config, distinct alphas per
class and per prime, L1 norms. Same protocol as alpha_analysis.py (r=3)."""
import re
from collections import defaultdict

BB = 15 * (1 << 27) + 1
P2 = 3 * (1 << 30) + 1
n, s, r = 64, 32, 5

def alpha_vec(O, m, B):
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, r)]
    a = [O[i] + s * d[i] for i in range(r)]
    cnt = [0] * n
    for i in range(r):
        for j in range(i + 1, r):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    for c in B:
        cnt[(2 * c) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    return tuple(cnt[k] - cnt[k + s] for k in range(s))

for fn, P, g0, tag in [("brute_r5_2013265921.txt", BB, 31, "BabyBear"),
                       ("brute_r5_3221225473.txt", P2, 5, "p2")]:
    h = pow(g0, (P - 1) // n, P)
    H = [pow(h, i, P) for i in range(n)]
    perclass = defaultdict(set)
    nconf = 0
    for line in open(fn):
        mm = re.match(r"SPUR_B O=([\d,]+) m=(\d+) B=([\d,]+)", line)
        if not mm:
            continue
        O = tuple(int(t) for t in mm.group(1).split(","))
        m = int(mm.group(2))
        B = [int(t) for t in mm.group(3).split(",")]
        v = alpha_vec(O, m, B)
        assert sum(c * H[k] for k, c in enumerate(v)) % P == 0
        perclass[(O, m)].add(v)
        nconf += 1
    alphas = defaultdict(int)
    for vs in perclass.values():
        for v in vs:
            alphas[v] += 1
    l1s = sorted(sum(abs(c) for c in v) for v in alphas)
    multi = sum(1 for vs in perclass.values() if len(vs) > 1)
    print(f"== {tag}: {nconf} explicit spurious configs, {len(perclass)} sampled "
          f"classes, {multi} classes with >1 distinct alpha ==")
    print(f"   distinct alpha vectors: {len(alphas)}; L1 norms: {l1s}")
    print(f"   alpha class-multiplicity (how many sampled classes share each): "
          f"{sorted(alphas.values(), reverse=True)}")
    print(f"   all alpha(zeta->H[1]) == 0 mod p VERIFIED")
