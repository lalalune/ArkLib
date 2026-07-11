"""TRIPLE-CHECK for r=5 (sampled flagged classes): same protocol as
verify_spurious.py but pattern (14,5). Reads SPUR_B lines from the class-mode
brute dumps (brute_r5_<p>.txt); for each explicit spurious (B, O, m) config,
verify by raw polynomial arithmetic mod p that it IS a genuine marginal
codeword (deg 34 monic, coeff X^33 = 0, coeff X^32 = LAM, agree exactly 33),
and is NOT char-0 balanced. Also re-verify the class-mode CLASS lines:
mitm == brute, genuine_bal == char0."""
import re, sys

BB = 15 * (1 << 27) + 1
P2 = 3 * (1 << 30) + 1
G0 = {BB: 31, P2: 5}
n, s, r = 64, 32, 5

def field(P):
    h = pow(G0[P], (P - 1) // n, P)
    H = [pow(h, i, P) for i in range(n)]
    assert len(set(H)) == n and H[s] == P - 1
    G = [H[(2 * c) % n] for c in range(s)]
    return H, G, H[s // 2], P - H[s // 2]

def polymul(a, b, P):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % P
    return out

def peval(e, x, P):
    acc = 0
    for c in reversed(e):
        acc = (acc * x + c) % P
    return acc

def check_one(P, O, m, B):
    H, G, ZS, LAM = field(P)
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, r)]
    a = [O[i] + s * d[i] for i in range(r)]
    x = [H[ai] for ai in a]
    xi = (P - sum(x) % P) % P
    e = [1]
    for c in sorted(B):
        e = polymul(e, [(P - G[c]) % P, 0, 1], P)
    for rt in x + [xi]:
        e = polymul(e, [(P - rt) % P, 1], P)
    assert len(e) == s + 3 and e[s + 2] == 1 and e[s + 1] == 0
    assert e[s] == LAM, "NOT a mod-p solution?!"
    zeros = [i for i in range(n) if peval(e, H[i], P) == 0]
    xiH = xi in set(H) or xi == 0
    assert len(zeros) == 33 + (1 if xiH else 0), (len(zeros), xiH)
    cnt = [0] * n
    for i in range(r):
        for j in range(i + 1, r):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    for c in B:
        cnt[(2 * c) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    vec = [cnt[k] - cnt[k + s] for k in range(s)]
    assert any(vec), "char-0 balanced -- not spurious?!"
    assert sum(v * H[k] for k, v in enumerate(vec)) % P == 0
    return xiH

fn, P = sys.argv[1], int(sys.argv[2])
nok, ncls, mismatch = 0, 0, 0
for line in open(fn):
    cm = re.match(r"CLASS .* char0=(\d+) mitm=(\d+) brute=(\d+) "
                  r"genuine_bal=(\d+) spurious=(\d+)", line)
    if cm:
        ncls += 1
        c0, mi, br, gb, sp = map(int, cm.groups())
        if not (mi == br and gb == c0 and sp == br - gb):
            mismatch += 1
            print("CLASS-LINE INCONSISTENT:", line.strip())
        continue
    mm = re.match(r"SPUR_B O=([\d,]+) m=(\d+) B=([\d,]+)", line)
    if not mm:
        continue
    O = tuple(int(t) for t in mm.group(1).split(","))
    m = int(mm.group(2))
    B = [int(t) for t in mm.group(3).split(",")]
    assert len(B) == 14 and not set(B) & set(O)
    check_one(P, O, m, B)
    nok += 1
print(f"{fn}: {ncls} sampled classes ALL with mitm==brute and genuine_bal==char0 "
      f"({mismatch} inconsistent); {nok} explicit spurious configs confirmed "
      f"by raw polynomial arithmetic (every SPUR_B line)")
assert mismatch == 0
