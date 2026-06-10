"""Cross-field falsification postpass: p = 3*2^30+1, g = 5, lam = -g^((p-1)/4).
Tests the level-2 conjecture's field-independence: l(w,18) = 35? l(w,17) = 1,344?
Same anatomy invariants (fiber pattern, equation, negation, B-census)?"""
import glob
from collections import Counter
from math import comb

P = 3221225473
g0 = 5
h32 = pow(g0, (P - 1) // 32, P)
H = [pow(h32, i, P) for i in range(32)]
h16 = h32 * h32 % P
G = [pow(h16, i, P) for i in range(16)]
hinv = pow(h32, P - 2, P)
inv32 = pow(32, P - 2, P)
LAM = (-pow(g0, (P - 1) // 4, P)) % P
HINVPOW = [pow(hinv, i, P) for i in range(32)]

w = [(pow(x, 18, P) + LAM * pow(x, 16, P)) % P for x in H]

def load(globpat):
    out = []
    for f in sorted(glob.glob(globpat)):
        for line in open(f):
            out.append(tuple(map(int, line.split())))
    return out

m18 = load("/tmp/level2/kb18_*.txt")
m17 = load("/tmp/level2/kb17_*.txt")
d18 = sorted(set(m18))
d17 = sorted(set(m17))
print(f"[KB] agree>=18: emissions {len(m18)}, distinct {len(d18)} "
      f"(expect 630 = 35*18 emissions, 35 distinct)")
print(f"[KB] agree==17: emissions {len(m17)}, distinct {len(d17)} (expect 1344, each once)")
print(f"[KB] disjoint: {not (set(d17) & set(d18))}")

def coeffs_idft(v):
    cs = []
    for d in range(32):
        s = 0
        for i in range(32):
            s += v[i] * HINVPOW[(d * i) % 32]
        cs.append(s % P * inv32 % P)
    return cs

# witness structure
zdeg = Counter()
ok = True
for v in d18:
    T = [i for i in range(32) if v[i] == w[i]]
    ok &= len(T) == 18 and all((i + 16) % 32 in T for i in T)
    S = {G[i % 16] for i in T}
    ok &= sum(S) % P == (P - LAM) % P
    zdeg.update({i % 16 for i in T})
print(f"[KB] all witnesses: agree-18, fiber-closed, e1(S) = -lam: {ok}")
zs = [z for z in range(16) if zdeg[z] == len(d18)]
print(f"[KB] z* candidates (in all): {zs}; G[z*] = {[G[z] for z in zs]}; "
      f"-lam = {(P-LAM)%P}  (z* should = -lam)")

pat = Counter()
eqfail = 0
fullsupp = 0
spread_ok = 0
s17 = set(d17)
negfree = 0
Bmult = Counter()
BO = set()
for v in d17:
    T = frozenset(i for i in range(32) if v[i] == w[i])
    assert len(T) == 17
    cs = coeffs_idft(list(v))
    assert all(c == 0 for c in cs[16:])
    if all(c != 0 for c in cs[:16]):
        fullsupp += 1
    B, X, O = [], [], []
    for z in range(16):
        a, b = z in T, (z + 16) in T
        if a and b: B.append(z)
        elif a: X.append(H[z]); O.append(z)
        elif b: X.append(H[z + 16]); O.append(z)
    pat[(len(B), len(O))] += 1
    if len(X) == 3:
        x1, x2, x3 = X
        e2 = (x1*x2 + x1*x3 + x2*x3) % P
        e1BO = (sum(G[b] for b in B) + sum(x*x % P for x in X)) % P
        if (e2 + e1BO + LAM) % P != 0:
            eqfail += 1
    Bmult[frozenset(B)] += 1
    BO.add((frozenset(B), frozenset(O)))
    vn = tuple(v[(i + 16) % 32] for i in range(32))
    if vn in s17 and vn != v:
        negfree += 1
print(f"[KB] full support: {fullsupp}/{len(d17)}")
print(f"[KB] fiber pattern histogram: {dict(sorted(pat.items()))}")
print(f"[KB] consistency equation failures: {eqfail}/{len(d17)}")
print(f"[KB] negation free pairs: {negfree}/{len(d17)} -> orbits {negfree//2 + (len(d17)-negfree)}")
print(f"[KB] distinct B: {len(Bmult)}; multiplicity histogram "
      f"{dict(sorted(Counter(Bmult.values()).items()))}")
print(f"[KB] distinct (B,O): {len(BO)}")
print(f"\n[VERDICT] field-independence of (35, 1344, anatomy): "
      f"{'CONFIRMED' if len(d18)==35 and len(d17)==1344 and eqfail==0 and dict(pat)=={(7,3):1344} else 'DIFFERS - CONJECTURE FALSIFIED/REFINED'}")

# index-level identity: are the agreement SETS (as mu32 index sets) literally the same
# as BabyBear's? (would mean the whole configuration is one characteristic-0 object)
PB = 2013265921
g0B = 31
h32B = pow(g0B, (PB - 1) // 32, PB)
HB = [pow(h32B, i, PB) for i in range(32)]
LAMB = 284861408
wB = [(pow(x, 18, PB) + LAMB * pow(x, 16, PB)) % PB for x in HB]
d17B = sorted(set(load("/tmp/n32census/audit_independent/my17_*.txt")))
d18B = sorted(set(load("/tmp/n32census/audit_independent/my18_*.txt")))
TB17 = {frozenset(i for i in range(32) if v[i] == wB[i]) for v in d17B}
TB18 = {frozenset(i for i in range(32) if v[i] == wB[i]) for v in d18B}
TK17 = {frozenset(i for i in range(32) if v[i] == w[i]) for v in d17}
TK18 = {frozenset(i for i in range(32) if v[i] == w[i]) for v in d18}
print(f"[INDEX] agree-17 T-sets identical across fields (as mu32 index sets): "
      f"{TB17 == TK17} ({len(TB17)} vs {len(TK17)})")
print(f"[INDEX] agree-18 T-sets identical across fields: {TB18 == TK18} "
      f"({len(TB18)} vs {len(TK18)})")
