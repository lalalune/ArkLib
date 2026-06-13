"""
EXACT field-norm computation for the falsifier's bad-alpha lattice.

alpha is an element of Z[zeta_64], zeta_64 a primitive 64th root of unity,
minimal polynomial Phi_64(x) = x^32 + 1 (degree phi(64)=32).
The falsifier emits alpha in the POWER BASIS reduced mod (x^32 + 1):
alpha = sum_{k=0}^{31} c_k zeta^k.

The field norm N(alpha) = prod_{sigma} sigma(alpha) = Res(x^32+1, alpha(x))
is an integer. The marginal-codeword SUPPLY transfers EXACTLY (mod-p surplus 0)
for a given prime p iff p does NOT divide N(alpha) for any bad alpha.
(Because the spurious config arises precisely when alpha(zeta->H[1]) == 0 mod p,
i.e. the prime ideal (p, zeta-H[1]) divides (alpha); summed over conjugates that
is p | N(alpha).)

We compute N(alpha) = det(M_alpha), where M_alpha is multiplication-by-alpha on
Z[x]/(x^32+1) in the power basis. Determinant via fraction-free Bareiss => EXACT.

Machine-light: pure python, single 32x32 integer determinant per alpha.
"""
import re
from collections import defaultdict

N = 64
D = 32  # phi(64) = degree of Phi_64 = x^32 + 1

def mul_matrix(c):
    """multiplication-by-alpha matrix on Z[x]/(x^32+1), power basis.
    column j = alpha * x^j reduced mod x^32+1.  x^32 == -1, so x^{32+k} == -x^k."""
    M = [[0]*D for _ in range(D)]
    for j in range(D):                 # basis element x^j
        # alpha * x^j = sum_k c_k x^{k+j}
        for k in range(D):
            ck = c[k]
            if ck == 0:
                continue
            e = k + j
            sign = 1
            while e >= D:
                e -= D
                sign = -sign           # x^32 = -1
            M[e][j] += sign * ck
    return M

def bareiss_det(mat):
    """Fraction-free Bareiss determinant, exact integers."""
    M = [row[:] for row in mat]
    n = len(M)
    sign = 1
    prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            # find pivot
            sw = -1
            for i in range(k+1, n):
                if M[i][k] != 0:
                    sw = i; break
            if sw == -1:
                return 0
            M[k], M[sw] = M[sw], M[k]
            sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n-1][n-1]

def norm(c):
    return bareiss_det(mul_matrix(c))

# ---- evaluation embedding to double-check p | N(alpha) at the actual prime ----
def alpha_eval_modp(c, h, p):
    return sum(ci * pow(h, k, p) for k, ci in enumerate(c)) % p

# ===== alpha vector reconstruction (matches alpha_analysis.py / _r5.py) =====
s = 32

def alpha_vec_r(O, m, B, r):
    d = [0] + [(m >> (i-1)) & 1 for i in range(1, r)]
    a = [O[i] + s*d[i] for i in range(r)]
    cnt = [0]*N
    for i in range(r):
        for j in range(i+1, r):
            cnt[(a[i]+a[j]) % N] += 1
    for o in O:
        cnt[(2*o) % N] += 1
    for ccc in B:
        cnt[(2*ccc) % N] += 1
    cnt[(3*s//2) % N] += 1
    return tuple(cnt[k] - cnt[k+s] for k in range(s))

BB = 15*(1<<27)+1
P2 = 3*(1<<30)+1

jobs = [
    ("brute_bb_r3.txt", BB, 31, "BabyBear", 3),
    ("brute_p2_r3.txt", P2, 5,  "p2",       3),
    ("brute_r5_2013265921.txt", BB, 31, "BabyBear", 5),
    ("brute_r5_3221225473.txt", P2, 5,  "p2",       5),
]

import sys
DIR = "/home/nubs/Git/ArkLib-232/scripts/probes/genlaw/falsifier/"

summary = {}
for fn, P, g0, tag, r in jobs:
    h = pow(g0, (P-1)//N, P)
    alphas = {}  # vec -> count of configs
    for line in open(DIR+fn):
        mm = re.match(r"SPUR_B O=([\d,]+) m=(\d+) B=([\d,]+)", line)
        if not mm:
            continue
        O = tuple(int(t) for t in mm.group(1).split(","))
        m = int(mm.group(2))
        B = [int(t) for t in mm.group(3).split(",")]
        v = alpha_vec_r(O, m, B, r)
        alphas[v] = alphas.get(v, 0) + 1
    # compute norms for distinct alphas
    rows = []
    for v in alphas:
        # sanity: alpha(h) == 0 mod P
        assert alpha_eval_modp(v, h, P) == 0, "alpha(h)!=0 mod p"
        Nv = norm(v)
        l1 = sum(abs(x) for x in v)
        rows.append((l1, Nv, v))
    rows.sort()
    # verify p | N for each
    bad = [r2 for r2 in rows if r2[1] % P != 0]
    norms_abs = sorted(abs(r2[1]) for r2 in rows)
    import math
    def log2abs(x):
        return math.log2(abs(x)) if x != 0 else float('-inf')
    print(f"===== {tag} r={r} (p={P} ~ 2^{math.log2(P):.2f}) =====")
    print(f"  distinct bad alpha: {len(rows)};  L1 norms: {sorted(r2[0] for r2 in rows)}")
    print(f"  |N(alpha)| log2 range: min={log2abs(norms_abs[0]):.2f}  "
          f"max={log2abs(norms_abs[-1]):.2f}  median={log2abs(norms_abs[len(norms_abs)//2]):.2f}")
    print(f"  p | N(alpha) holds for ALL: {len(bad)==0}  (violations: {len(bad)})")
    # print a few explicit (smallest and largest by |N|)
    by_n = sorted(rows, key=lambda t: abs(t[1]))
    for label, rr in [("min|N|", by_n[0]), ("max|N|", by_n[-1])]:
        l1, Nv, v = rr
        supp = {k:cc for k,cc in enumerate(v) if cc}
        print(f"    {label}: L1={l1}  N={Nv}  (|N|=2^{log2abs(Nv):.2f})  "
              f"p|N: {Nv % P == 0}")
        print(f"       support={supp}")
    summary[(tag,r)] = dict(count=len(rows),
                            l1=sorted(r2[0] for r2 in rows),
                            logmin=log2abs(norms_abs[0]),
                            logmax=log2abs(norms_abs[-1]),
                            logmed=log2abs(norms_abs[len(norms_abs)//2]),
                            all_div=(len(bad)==0))
    print()

print("==== SUMMARY (supply transfer threshold = max |N(alpha)| over bad lattice) ====")
import math
for k, v in summary.items():
    print(f"  {k}: {v['count']} alphas, max|N|=2^{v['logmax']:.1f}, "
          f"min|N|=2^{v['logmin']:.1f}, all p|N: {v['all_div']}")
print(f"\n  BabyBear p = 2^{math.log2(BB):.2f}; p2 = 2^{math.log2(P2):.2f}; "
      f"Goldilocks 2^64-2^32+1 = 2^{math.log2((1<<64)-(1<<32)+1):.4f}")
print(f"  energy threshold n^2.3 for n=64: 2^{2.3*6:.2f} = {int(64**2.3)}")
print(f"  energy threshold n^2.5 for n=64: 2^{2.5*6:.2f} = {int(64**2.5)}")
