"""AUDITOR n=64: (A) field verification at BabyBear of MY enumerated classes
(r=3, r=5, witness, negatives); (B) full census expansion + cross-checks vs
both agents' claims (and set-equality vs verifier's n64_sols.json for r=3).
"""
import json, random, re
from itertools import combinations
from collections import Counter, defaultdict
from math import comb

random.seed(99)
P = 15 * (1 << 27) + 1
g0 = 31
n, s, A = 64, 32, 16
zeta = pow(g0, (P - 1) // n, P)
H = [pow(zeta, i, P) for i in range(n)]
assert len(set(H)) == n
ZS = H[16]
assert pow(ZS, 2, P) == P - 1
LAM = (P - ZS) % P
Hset = set(H)
w = [(pow(x, 34, P) + LAM * pow(x, 32, P)) % P for x in H]

def load(fn, r):
    recs = []
    for line in open(fn):
        if not line.startswith("REC"):
            continue
        head, m, hpart, vpart, wpart = line.split("|")
        O = tuple(int(x) for x in head.split()[1:1 + r])
        m = int(m)
        forced = tuple(int(x) for x in hpart.split()[3:])
        free = tuple(int(x) for x in vpart.split()[3:])
        wv = int(wpart.split()[1])
        recs.append((O, m, forced, free, wv))
    return recs

r3 = load("/tmp/genlaw/audit/recs_s32_r3.txt", 3)
r5 = load("/tmp/genlaw/audit/recs_s32_r5.txt", 5)

# ---------- (A) field checks ----------
def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r

def peval(e, x):
    acc = 0
    for c in reversed(e):
        acc = (acc * x + c) % P
    return acc

def field_check(O, m, forced, free, r, bsz, flip=0, perturb=False):
    k = (bsz - len(forced)) // 2
    pick = random.sample(list(free), k)
    B = sorted(set(forced) | {c for c in pick} | {c + A for c in pick})
    d = [flip] + [((m >> (i - 1)) & 1) ^ flip for i in range(1, r)]
    if perturb:
        d[1] ^= 1                      # break one sign -> should fail
    X = [H[(O[i] + s * d[i]) % n] for i in range(r)]
    xi = (-sum(X)) % P
    roots = []
    for b in B:
        roots += [H[b], H[b + s]]
    roots += X + [xi]
    e = [1]
    for rt in roots:
        e = polymul(e, [(-rt) % P, 1])
    assert len(e) == s + 3 and e[s + 2] == 1 and e[s + 1] == 0
    if perturb:
        return e[s] == LAM             # should be False
    assert e[s] == LAM, "consistency FAILS in field for enumerated class"
    assert xi != 0 and xi not in Hset, "L4 fails mod p"
    zeros = sorted(i for i in range(n) if peval(e, H[i]) == 0)
    Tpred = sorted([b for b in B] + [b + s for b in B]
                   + [(O[i] + s * d[i]) % n for i in range(r)])
    assert zeros == Tpred and len(zeros) == s + 1, f"zeros {len(zeros)}"
    return True

ok3 = sum(field_check(*rec[:4], 3, 15, flip=f) for rec in random.sample(r3, 12)
          for f in (0, 1))
print(f"[A] r=3: {ok3}/24 sampled elements are genuine agree-EXACTLY-33 errors")
ok5 = sum(field_check(*rec[:4], 5, 14, flip=f) for rec in random.sample(r5, 12)
          for f in (0, 1))
print(f"[A] r=5: {ok5}/24 sampled elements are genuine agree-EXACTLY-33 errors")

# witness layer: S = fiber 8 + 8 antipodal axis-pairs from the 15 non-z* axes
for _ in range(5):
    pick = random.sample([c for c in range(16) if c != 8], 8)
    S = [8] + [z for c in pick for z in (c, c + 16)]
    roots = [H[z] for z in S] + [H[z + 32] for z in S]
    e = [1]
    for rt in roots:
        e = polymul(e, [(-rt) % P, 1])
    assert e[s + 2] == 1 and e[s + 1] == 0 and e[s] == LAM
    zeros = sum(1 for i in range(n) if peval(e, H[i]) == 0)
    assert zeros == s + 2, zeros
print("[A] witness: 5/5 sampled S give agree-EXACTLY-34")

# negatives: perturbed signs of true classes + random configs
bad = 0
for rec in random.sample(r3, 13):
    bad += not field_check(*rec[:4], 3, 15, perturb=True)
for rec in random.sample(r5, 12):
    bad += not field_check(*rec[:4], 5, 14, perturb=True)
print(f"[A] negatives: {bad}/25 sign-perturbed configs correctly FAIL e[32]=lam")
assert ok3 == 24 and ok5 == 24 and bad == 25

# ---------- (B) census expansion ----------
def expand(recs, bsz):
    sols = []
    for O, m, forced, free, wv in recs:
        k = (bsz - len(forced)) // 2
        base = 0
        for f in forced:
            base |= 1 << f
        cnt = 0
        for pick in combinations(free, k):
            B = base
            for c in pick:
                B |= (1 << c) | (1 << (c + A))
            sols.append((B, O, m))
            cnt += 1
        assert cnt == wv
    return sols

S3 = expand(r3, 15)
print(f"\n[B] r=3 expanded: {len(S3)} (B,O,sigma) classes -> {2*len(S3)} elements")
assert len(S3) == 764544

hvk = Counter()
hvkw = Counter()
for O, m, forced, free, wv in r3:
    h, v = len(forced), len(free)
    k = (15 - h) // 2
    hvk[(h, v, k)] += 1
    hvkw[(h, v, k)] += wv
print(f"[B] r=3 strata classes: {dict(sorted(hvk.items()))}")
print(f"[B] r=3 strata ways:    {dict(sorted(hvkw.items()))}")
VER = {(1,13,7): (4, 6864), (3,11,6): (96, 44352), (3,12,6): (100, 92400),
       (5,10,5): (1056, 266112), (5,11,5): (288, 133056), (7,9,4): (1760, 221760)}
assert all(hvk[k] == c and hvkw[k] == ww for k, (c, ww) in VER.items())
print("[B] r=3 strata == verifier's table EXACTLY")

epsc = Counter(O[0] % 2 for B, O, m in S3)
print(f"[B] r=3 eps split (classes): {dict(epsc)} (claim: 373440/391104)")
assert epsc[0] == 373440 and epsc[1] == 391104
pure3 = all(len({o % 2 for o in O}) == 1 for B, O, m in S3)
BO = defaultdict(set)
for B, O, m in S3:
    BO[(B, O)].add(m)
sig_u = all(len(v) == 1 for v in BO.values())
Bc = Counter(B for B, O, m in S3)
hist = Counter(Bc.values())
print(f"[B] r=3 parity-pure: {pure3}; sigma-unique per (B,O): {sig_u}; "
      f"distinct B: {len(Bc)}; hist: {dict(hist)}")
assert pure3 and sig_u and len(Bc) == 703656 and hist[1] == 642768 and hist[2] == 60888
perB = defaultdict(list)
for B, O, m in S3:
    perB[B].append(set(O))
dual = [v for v in perB.values() if len(v) == 2]
disj = sum(1 for v in dual if not (v[0] & v[1]))
share2 = sum(1 for v in dual if len(v[0] & v[1]) == 2)
print(f"[B] r=3 dual-B: {len(dual)} (disjoint {disj}, share2 {share2})")
assert len(dual) == 60888 and disj == 46368 and share2 == 14520

S5 = expand(r5, 14)
print(f"\n[B] r=5 expanded: {len(S5)} classes -> {2*len(S5)} elements")
assert len(S5) == 99512
eps5 = Counter(O[0] % 2 for B, O, m in S5)
pure5 = all(len({o % 2 for o in O}) == 1 for B, O, m in S5)
BO5 = defaultdict(set)
for B, O, m in S5:
    BO5[(B, O)].add(m)
sig_u5 = all(len(v) == 1 for v in BO5.values())
Bc5 = Counter(B for B, O, m in S5)
print(f"[B] r=5 eps split: {dict(eps5)} (claim 49768/49744); parity-pure: {pure5}; "
      f"sigma-unique: {sig_u5}; distinct B: {len(Bc5)}; hist: {dict(Counter(Bc5.values()))}")
assert eps5[0] == 49768 and eps5[1] == 49744 and pure5 and sig_u5
assert len(Bc5) == 99512 and set(Counter(Bc5.values())) == {1}
# L3-break census: classes where a product lands on the -z* fiber (24)
l3b = 0
pairs5 = list(combinations(range(5), 2))
for O, m, forced, free, wv in r5:
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, 5)]
    a = [O[i] + s * d[i] for i in range(5)]
    hit = any((a[i] + a[j]) % n == 48 for i, j in pairs5)
    l3b += hit * wv
print(f"[B] r=5 classes with a product ON the -z* slot (L3 broken): {l3b} "
      f"(= generalizer's LP|OP 288 + BP|LP 2496; its 'L3_breaks' note names only LP|OP)")
assert l3b == 288 + 2496

# cross-set equality vs verifier's n64_sols.json (r=3)
ver = json.load(open("/tmp/genlaw/n64_sols.json"))
def tomask(lst):
    b = 0
    for x in lst:
        b |= 1 << x
    return b
vs = {(tomask(B), tuple(O), tuple(sg)) for B, O, sg in ver}
# verifier sig encoding: sig=(s12,s13,s23) tuples from SIGS; map to my mask m:
# their d = (0, sig[0], sig[1]) -> my m = sig[0] + 2*sig[1]
vs2 = {(B, O, sg[0] + 2 * sg[1]) for B, O, sg in vs}
mine = set(S3)
print(f"\n[B] r=3 EXACT SET EQUALITY with verifier's n64_sols.json: {mine == vs2} "
      f"({len(mine)} vs {len(vs2)})")
assert mine == vs2
print("\nAUDIT FIELD+CENSUS: ALL PASS")
