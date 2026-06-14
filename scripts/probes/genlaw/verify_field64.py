"""FIELD VERIFICATION at n=64 (BabyBear, 64 | 2^27): construct e from sampled
balanced configs of BOTH strata (r=3 engine and r=5 anatomy) and verify each is
a genuine agree-EXACTLY-33 error for w = X^34 + lam X^32, lam = -z*.
Also verify the witness-layer law: sampled S (z*-fiber + 8 antipodal pairs from
the 15 non-z* axes) give agree-exactly-34 errors, and a non-conforming S fails.
"""
import random, sys
from itertools import combinations
from math import comb
sys.path.insert(0, '/tmp/genlaw')

P = 15 * (1 << 27) + 1
g0 = 31
s, n = 32, 64
h = pow(g0, (P - 1) // n, P)
H = [pow(h, i, P) for i in range(n)]
assert len(set(H)) == n and pow(h, s, P) == P - 1
ZS = H[s // 2]                       # z* = zeta^16, 4th root of unity
assert pow(ZS, 2, P) == P - 1
LAM = P - ZS
G = [H[(2 * z) % n] for z in range(s)]     # fibers z_b = zeta^{2b}

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r

def build_e(roots):
    e = [1]
    for rt in roots:
        e = polymul(e, [(-rt) % P, 1])
    return e

def check(roots, expect_agree):
    e = build_e(roots)
    deg = len(e) - 1
    assert deg == s + 2 and e[-1] == 1
    assert e[s + 1] == 0, "e1(roots) != 0"
    assert e[s] == LAM, "consistency e2 = lam FAILS"
    agree = sum(1 for x in H if sum(c * pow(x, i, P) for i, c in enumerate(e)) % P == 0)
    assert agree == expect_agree, (agree, expect_agree)
    return True

random.seed(232)

# ---- r=3 stratum samples from the engine ----
from engine import run
R = run(32)
samp3 = random.sample(R['sols'], 12)
for B, O, sig in samp3:
    d = (0, sig[0], sig[1])
    X = [H[(O[i] + s * d[i]) % n] for i in range(3)]
    xi = (-(X[0] + X[1] + X[2])) % P
    assert xi != 0 and xi not in H                     # L4 at n=64
    roots = []
    for b in B:
        roots += [H[b], H[b + s]]
    roots += X + [xi]
    check(roots, s + 1)
print("[F64] 12/12 sampled r=3 configs: genuine agree-EXACTLY-33 errors at BabyBear")

# ---- r=5 stratum samples (re-derive a batch of solutions, sample) ----
r5 = []
pairs5 = list(combinations(range(5), 2))
cnt_target = 0
for O in combinations(range(s), 5):
    Oset = set(O)
    for m in range(1 << 4):
        a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, 5)]
        cnt = [0] * n
        for (i, j) in pairs5:
            cnt[(a[i] + a[j]) % n] += 1
        for o in O:
            cnt[(2 * o) % n] += 1
        cnt[48] += 1
        if any(cnt[mm] != cnt[mm + s] for mm in range(1, s, 2)):
            continue
        ok, forced, freeax = True, [], []
        for c in range(16):
            dd = cnt[2 * c] - cnt[(2 * c + s) % n]
            if abs(dd) >= 2:
                ok = False; break
            if dd == -1:
                f = c
            elif dd == 1:
                f = c + 16
            else:
                if c not in Oset and (c + 16) not in Oset:
                    freeax.append(c)
                continue
            if f in Oset:
                ok = False; break
            forced.append(f)
        if not ok:
            continue
        b5 = 14
        hh, vv = len(forced), len(freeax)
        if (b5 - hh) < 0 or (b5 - hh) % 2 or (b5 - hh) // 2 > vv:
            continue
        for pick in combinations(freeax, (b5 - hh) // 2):
            B = frozenset(forced) | set(pick) | {c + 16 for c in pick}
            r5.append((B, O, m))
    if len(r5) > 4000:
        break
samp5 = random.sample(r5, 12)
for B, O, m in samp5:
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, 5)]
    X = [H[(O[i] + s * d[i]) % n] for i in range(5)]
    xi = (-sum(X)) % P
    assert xi != 0 and xi not in H
    roots = []
    for b in B:
        roots += [H[b], H[b + s]]
    roots += X + [xi]
    check(roots, s + 1)
print("[F64] 12/12 sampled r=5 configs: genuine agree-EXACTLY-33 errors at BabyBear")
print("      (the NEW stratum is REAL in the field, not just balance-combinatorics)")

# ---- witness layer: S = {8} U 8 antipodal pairs from the 15 non-z* axes ----
axes = [c for c in range(16) if c != 8]
for trial in range(5):
    pick = random.sample(axes, 8)
    S = [8] + [z for c in pick for z in (c, c + 16)]
    roots = [H[z] for z in S] + [H[z + 32] for z in S]
    e = build_e(roots)
    assert e[s + 1] == 0 and e[s] == LAM
    agree = sum(1 for x in H if sum(c * pow(x, i, P) for i, c in enumerate(e)) % P == 0)
    assert agree == s + 2, agree
print("[F64] 5/5 sampled witness S (z*-fiber + 8 pairs / C(15,8) law): agree-exactly-34")
bad = [8] + [z for c in random.sample(axes, 7) for z in (c, c + 16)] + [0, 5]
roots = [H[z] for z in set(bad)] + [H[z + 32] for z in set(bad)]
e = build_e(roots)
print(f"[F64] non-conforming S control: e2 == lam ? {e[s] == LAM} (must be False)")
assert e[s] != LAM
print("FIELD VERIFICATION COMPLETE")
