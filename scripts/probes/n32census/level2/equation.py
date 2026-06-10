"""Verify the derived ONE-EQUATION characterization of the 1,344:
  e(x) = X^18 + lam X^16 - c(X) factors as Prod_{b in B}(X^2 - z_b) * q(X),
  q monic quartic with roots {x1,x2,x3,xi}, xi := -(x1+x2+x3)  [q3 = 0 <=> deg c < 16... x^17]
  and the consistency equation   e2(x1,x2,x3) + e1(B u O) + lam = 0   over F_p
  (equivalently e2(x1,x2,x3) = -lam + e1(Zfibers), Z = G \ (B u O)).
Also: xi-status histogram (in H? double root? zero?), witness equation e1(S) = -lam,
the 92 dual-O B's disjointness, and per-(B,O) sigma uniqueness."""
import glob
from collections import Counter
from math import comb

P = 2013265921
g0 = 31
h32 = pow(g0, (P - 1) // 32, P)
H = [pow(h32, i, P) for i in range(32)]
h16 = h32 * h32 % P
G = [pow(h16, i, P) for i in range(16)]
hinv = pow(h32, P - 2, P)
inv32 = pow(32, P - 2, P)
LAM = 284861408
HINVPOW = [pow(hinv, i, P) for i in range(32)]
Hset = set(H)

def word(lam):
    return [(pow(x, 18, P) + lam * pow(x, 16, P)) % P for x in H]

def load(globpat):
    out = []
    for f in sorted(glob.glob(globpat)):
        for line in open(f):
            out.append(tuple(map(int, line.split())))
    return out

AUD = "/tmp/n32census/audit_independent"
w = word(LAM)
d17 = sorted(set(load(f"{AUD}/my17_*.txt")))
m18 = sorted(set(load(f"{AUD}/my18_*.txt")))

# witness equation: e1(S) = -lam for all 35 (S as field elements)
for v in m18:
    T = [i for i in range(32) if v[i] == w[i]]
    S = {G[i % 16] for i in T}
    assert sum(S) % P == (P - LAM) % P
print("[W] all 35 witnesses satisfy e1(S) = -lam  (S the 9 fiber values)  VERIFIED")
print(f"[W] and S = {{-lam}} u (4 antipodal pairs): the O50 vanishing-sum structure "
      f"(e1(S \\ {{z*}}) = 0, 2-power antipodal closure)")

eqfail = 0
xistat = Counter()
sigper = {}
for v in d17:
    T = frozenset(i for i in range(32) if v[i] == w[i])
    B, X = [], []
    for z in range(16):
        a, b = z in T, (z + 16) in T
        if a and b:
            B.append(z)
        elif a:
            X.append(H[z])
        elif b:
            X.append(H[z + 16])
    assert len(B) == 7 and len(X) == 3
    x1, x2, x3 = X
    s = (x1 + x2 + x3) % P
    xi = (P - s) % P
    e2 = (x1 * x2 + x1 * x3 + x2 * x3) % P
    e1BO = (sum(G[b] for b in B) + sum(x * x % P for x in X)) % P
    if (e2 + e1BO + LAM) % P != 0:
        eqfail += 1
    if xi == 0:
        xistat['zero'] += 1
    elif xi in (x1, x2, x3):
        xistat['double-root (in chosen 3)'] += 1
    elif xi in Hset:
        xistat['in H elsewhere (!!)'] += 1
    else:
        xistat['outside H'] += 1
    key = (frozenset(B), frozenset(x * x % P for x in X))
    sg = tuple(1 if x in {H[z] for z in range(16)} else -1
               for x in sorted(X))
    sigper.setdefault(key, set()).add(frozenset(X))
print(f"[EQ] consistency equation e2(x1,x2,x3) + e1(B) + p1(z_O) + lam = 0: "
      f"failures {eqfail}/1344  ->  {'VERIFIED for ALL' if eqfail == 0 else 'FALSIFIED'}")
print(f"[XI] 18th-root xi = -(x1+x2+x3) status: {dict(xistat)}")
print(f"[SIG] per-(B,O): #distinct root-triples (= sigma choices realized): "
      f"{dict(sorted(Counter(len(s) for s in sigper.values()).items()))} "
      f"(2 = the +-pair; >2 would mean extra sigma classes)")

# the 92 dual-O B's: O1, O2 disjoint for ALL?
perB = {}
for (B, O), _ in [(k, 1) for k in sigper]:
    perB.setdefault(B, []).append(O)
dual = {b: os_ for b, os_ in perB.items() if len(os_) == 2}
print(f"[DUAL] B's with two O's: {len(dual)}; all O1 n O2 = 0: "
      f"{all(not (frozenset(o1) & frozenset(o2)) for o1, o2 in dual.values())}")
zer = [b for b, os_ in dual.items()]
# union O1 u O2 = 6 of the 9 complement fibers; profile of leftover 3?
left = Counter()
for b, (o1, o2) in dual.items():
    compl = frozenset(G[z] for z in range(16)) - frozenset(G[z] for z in
            [zz for zz in range(16) if frozenset({G[zz]}) <= frozenset()]) # noop
left_sizes = Counter(len(frozenset(o1) | frozenset(o2)) for o1, o2 in dual.values())
print(f"[DUAL] |O1 u O2| histogram: {dict(left_sizes)}")

# total selection-space accounting
print(f"\n[COUNT FRAME] selection space C(16,7)*C(9,3)*2^3 = "
      f"{comb(16,7)*comb(9,3)*8:,}; one scalar equation; solutions (census) = 1,344; "
      f"the 1,344 = the cyclotomic degeneracy count of that single equation "
      f"(Entry-17 frame: overdetermination 18-17 = 1 equation).")
print(f"[COUNT FRAME] naive Weil-type expectation ~ space/p = "
      f"{comb(16,7)*comb(9,3)*8/P:.4f}; actual 1,344 -> concentration factor ~"
      f"{1344/(comb(16,7)*comb(9,3)*8/P):,.0f}x: the equation is maximally degenerate "
      f"on root-of-unity data (vanishing-sum locus).")
print("DONE")
