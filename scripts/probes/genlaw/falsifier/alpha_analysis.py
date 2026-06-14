"""Light analysis of the confirmed r=3 spurious configs: the char-0 lattice
vector alpha (power basis of Z[zeta_64], zeta^{k+32} = -zeta^k) per config,
its L1 norm, distinct alphas per class, and the prime factorization role:
alpha(h) = 0 mod p means p divides the integer Res-type value; we report
the distinct alpha vectors so the mechanism is on the record."""
import re
from collections import defaultdict

BB = 15 * (1 << 27) + 1
P2 = 3 * (1 << 30) + 1
n, s = 64, 32

def alpha_vec(O, m, B):
    d = (0, m & 1, (m >> 1) & 1)
    a = [O[i] + s * d[i] for i in range(3)]
    cnt = [0] * n
    for i in range(3):
        for j in range(i + 1, 3):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    for c in B:
        cnt[(2 * c) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    return tuple(cnt[k] - cnt[k + s] for k in range(s))

for fn, P, tag in [("brute_bb_r3.txt", BB, "BabyBear"), ("brute_p2_r3.txt", P2, "p2")]:
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
        perclass[(O, m)].add(v)
        nconf += 1
    print(f"== {tag} (p={P}): {nconf} spurious configs in {len(perclass)} classes ==")
    for (O, m), vs in sorted(perclass.items()):
        for v in vs:
            # verify alpha(h)=0 mod p once more, and show support
            g0 = 31 if P == BB else 5
            h = pow(g0, (P - 1) // n, P)
            H = [pow(h, i, P) for i in range(n)]
            assert sum(c * H[k] for k, c in enumerate(v)) % P == 0
            supp = {k: c for k, c in enumerate(v) if c}
            print(f"  O={O} m={m}: alpha {supp} (L1={sum(abs(c) for c in v)}) "
                  f"-> alpha(zeta->H[1]) == 0 mod p VERIFIED")
    print()
