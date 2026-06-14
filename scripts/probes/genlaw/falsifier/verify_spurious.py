"""TRIPLE-CHECK stage 3: for every explicitly dumped spurious (B, O, m) config,
independently (pure Python, full polynomial arithmetic, construct_n64.py
conventions) verify that
  (1) e = Prod_{c in B}(X^2-G[c]) (X-x1)(X-x2)(X-x3)(X-xi) is monic deg 34 with
      coeff(X^33) = 0 and coeff(X^32) = LAM  ==>  c = w - e IS a genuine
      deg<32 RS codeword mod p whose agreement set with w contains T;
  (2) the agreement count is exactly 33 (or 34 if xi slipped into mu_64);
  (3) the config is NOT char-0 balanced (alpha != 0 in Z[zeta_64]) -- i.e. it
      is genuinely spurious, NOT a missed char-0 solution;
  (4) the char-0 alpha, embedded mod p, is 0 (the mechanism: p | alpha under
      zeta -> H[1]).
"""
import re, sys
from math import comb

BB = 15 * (1 << 27) + 1
P2 = 3 * (1 << 30) + 1
G0 = {BB: 31, P2: 5, 97: 5, 193: 5}
n, s = 64, 32

def field(P):
    g0 = G0[P]
    h = pow(g0, (P - 1) // n, P)
    H = [pow(h, i, P) for i in range(n)]
    assert len(set(H)) == n and H[s] == P - 1
    G = [H[(2 * c) % n] for c in range(s)]
    ZS = H[s // 2]
    LAM = P - ZS
    w = [(pow(x, s + 2, P) + LAM * pow(x, s, P)) % P for x in H]
    return H, G, ZS, LAM, w

def polymul(a, b, P):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r

def peval(e, x, P):
    acc = 0
    for c in reversed(e):
        acc = (acc * x + c) % P
    return acc

def check_one(P, O, m, B):
    H, G, ZS, LAM, w = field(P)
    d = (0, m & 1, (m >> 1) & 1)
    a = [O[i] + s * d[i] for i in range(3)]
    x = [H[ai] for ai in a]
    xi = (P - sum(x) % P) % P
    e = [1]
    for c in sorted(B):
        e = polymul(e, [(P - G[c]) % P, 0, 1], P)
    for rt in x + [xi]:
        e = polymul(e, [(P - rt) % P, 1], P)
    assert len(e) == s + 3 and e[s + 2] == 1, "not monic deg 34"
    assert e[s + 1] == 0, "coeff X^33 != 0"
    assert e[s] == LAM, "NOT actually a mod-p solution -- C code wrong?!"
    # c = w - e is a genuine deg<32 codeword; agreement = zeros of e on H
    zeros = [i for i in range(n) if peval(e, H[i], P) == 0]
    Tpred = sorted([c for c in B] + [c + s for c in B] + a)
    assert set(Tpred) <= set(zeros)
    agree = len(zeros)
    xiH = xi in set(H) or xi == 0
    assert agree == 33 + (1 if xiH else 0), (agree, xiH)
    # char-0 multiset alpha: products + O_z + B_z + {-z*}, exponents in Z_64
    cnt = [0] * n
    for i in range(3):
        for j in range(i + 1, 3):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    for c in B:
        cnt[(2 * c) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    # alpha as power-basis vector over zeta^0..zeta^31 (zeta^{k+32} = -zeta^k)
    vec = [cnt[k] - cnt[k + s] for k in range(s)]
    assert any(vec), "config IS char-0 balanced -- placement rule missed it?!"
    alpha_p = sum(v * H[k] for k, v in enumerate(vec)) % P
    assert alpha_p == 0, "alpha != 0 mod p but equation held?!"
    return agree, xiH, vec

tot = 0
for fn, P in [("brute_bb_r3.txt", BB), ("brute_p2_r3.txt", P2)]:
    nf = 0
    for line in open(fn):
        mm = re.match(r"SPUR_B O=([\d,]+) m=(\d+) B=([\d,]+)", line)
        if not mm:
            continue
        O = tuple(int(t) for t in mm.group(1).split(","))
        m = int(mm.group(2))
        B = [int(t) for t in mm.group(3).split(",")]
        assert len(B) == 15 and not set(B) & set(O)
        agree, xiH, vec = check_one(P, O, m, B)
        nf += 1
        tot += 1
        print(f"p={P} O={O} m={m} B={B}: GENUINE mod-p marginal codeword, "
              f"agree={agree}, xi_in_H={xiH}, char0 alpha vec nonzero "
              f"(L1 {sum(abs(v) for v in vec)})")
    print(f"== {fn}: {nf}/{nf} spurious configs independently CONFIRMED ==")
print(f"TOTAL {tot} spurious configs confirmed by raw polynomial arithmetic")
