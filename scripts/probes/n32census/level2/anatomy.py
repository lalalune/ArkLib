"""LEVEL-2 ANATOMY of the 1,344 agree-exactly-17 elements of the canonical n=32 max-fiber word.
The n=32 analogue of the C19/Entry-12-13 anatomy (DISPROOF_LOG O12''-O13, O63, O87).

Pipeline (per word: canonical lam=284861408, alt lam=p-1):
  A. load + hard re-verify the 1,344 (distinct, agree exactly 17, deg<16, disjoint from 35)
  B. IDFT coefficients; full-support check; O63 ceiling-halving spread chart depths 1,2,3
     (error e = X^18 + lam X^16 - c : support = supp(c) u {16,18}); witness chart as calibration
  C. Entry-12/13 witness-overlap: |T n T_S| profiles vs all 35 witness sets; region-lattice atoms
     (on H across 35 T_S, and on G across the 35 fiber 9-subsets S)
  D. descent anatomy: fiber both/one/zero pattern (B,O,sigma); forced forms c_o = gamma*Pi_B,
     c_e = I_B(v2) + alpha*Pi_B; B-set census + B-vs-S relations
  E. symmetry: negation x->-x orbit structure on the 1,344; canonical->alt rotation transport
"""
import glob, sys
from collections import Counter
from itertools import combinations
from math import comb

P = 2013265921
g0 = 31
h32 = pow(g0, (P - 1) // 32, P)
H = [pow(h32, i, P) for i in range(32)]
h16 = h32 * h32 % P
G = [pow(h16, i, P) for i in range(16)]          # G[i] = H[i]^2 = H[i+16]^2
hinv = pow(h32, P - 2, P)
inv32 = pow(32, P - 2, P)
LAM = 284861408
LAM_ALT = P - 1
HPOW = [pow(h32, i, P) for i in range(32)]
HINVPOW = [pow(hinv, i, P) for i in range(32)]

def word(lam):
    return [(pow(x, 18, P) + lam * pow(x, 16, P)) % P for x in H]

def coeffs_idft(v):
    cs = []
    for d in range(32):
        s = 0
        for i in range(32):
            s += v[i] * HINVPOW[(d * i) % 32]
        cs.append(s % P * inv32 % P)
    return cs

def load(globpat):
    out = []
    for f in sorted(glob.glob(globpat)):
        for line in open(f):
            out.append(tuple(map(int, line.split())))
    return out

# ---- O63 ceiling-halving digit code (odd e -> (e+1)/2, even e -> e/2) ----
def digcode(e, depth):
    ds = []
    for _ in range(depth):
        d = e & 1
        ds.append(d)
        e = (e + d) >> 1
    return tuple(ds)

def spread(supp, depth):
    return len({digcode(x, depth) for x in supp})

# ---- polynomial helpers over F_p ----
def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r

def polyeval(cs, x):
    acc = 0
    for c in reversed(cs):
        acc = (acc * x + c) % P
    return acc

def lagrange(pts):  # [(x,y)] -> coeff list deg < len(pts)
    n = len(pts)
    cs = [0] * n
    for i, (xi, yi) in enumerate(pts):
        num = [1]
        den = 1
        for j, (xj, _) in enumerate(pts):
            if j != i:
                num = polymul(num, [(-xj) % P, 1])
                den = den * ((xi - xj) % P) % P
        f = yi * pow(den, P - 2, P) % P
        for d in range(len(num)):
            cs[d] = (cs[d] + num[d] * f) % P
    return cs

AUD = "/tmp/n32census/audit_independent"

def anatomize(tag, lam, f17, f18):
    print(f"\n{'='*78}\n== WORD {tag}: lam = {lam}\n{'='*78}")
    w = word(lam)
    m17 = load(f"{AUD}/{f17}")
    m18 = sorted(set(load(f"{AUD}/{f18}")))
    d17 = sorted(set(m17))
    print(f"[A] agree-17 emissions {len(m17)}, distinct {len(d17)}, "
          f"witnesses distinct {len(m18)}, disjoint: {not (set(d17) & set(m18))}")
    assert len(m17) == len(d17) == 1344 and len(m18) == 35

    # hard re-verify every element: agreement EXACTLY 17, deg < 16
    coeffs = {}
    Ts = {}
    for v in d17:
        T = frozenset(i for i in range(32) if v[i] == w[i])
        assert len(T) == 17, f"agreement {len(T)}"
        cs = coeffs_idft(list(v))
        assert all(c == 0 for c in cs[16:]), "not deg<16"
        coeffs[v] = cs[:16]
        Ts[v] = T
    TS = {}
    Ssets = {}
    for v in m18:
        T = frozenset(i for i in range(32) if v[i] == w[i])
        assert len(T) == 18
        cs = coeffs_idft(list(v))
        assert all(c == 0 for c in cs[16:])
        # fiber-closed?
        assert all((i + 16) % 32 in T for i in T), "witness set not fiber-closed"
        TS[v] = T
        Ssets[v] = frozenset(i % 16 for i in T)
        assert len(Ssets[v]) == 9
    print(f"[A] all 1344 re-verified agree==17 & deg<16; all 35 re-verified agree==18, "
          f"fiber-closed (9-subsets S of G)")

    # ---- B. support + O63 spread chart ----
    fullsupp = sum(1 for v in d17 if all(c != 0 for c in coeffs[v]))
    print(f"[B] full 16-coefficient support: {fullsupp}/1344")
    sp = {1: Counter(), 2: Counter(), 3: Counter()}
    cls3 = Counter()
    for v in d17:
        supp = {j for j in range(16) if coeffs[v][j]} | {16, 18}
        for dep in (1, 2, 3):
            sp[dep][spread(supp, dep)] += 1
        cls3[frozenset(digcode(x, 3) for x in supp)] += 1
    print(f"[B] O63 spread chart of the 1344: depth1 {dict(sp[1])}  depth2 {dict(sp[2])}  "
          f"depth3 {dict(sp[3])}")
    print(f"[B] distinct depth-3 occupied-class SETS: {len(cls3)}")
    # witness calibration chart
    wsp = {1: Counter(), 2: Counter(), 3: Counter()}
    for v in m18:
        cs = coeffs_idft(list(v))
        supp = {j for j in range(16) if cs[j]} | {16, 18}
        for dep in (1, 2, 3):
            wsp[dep][spread(supp, dep)] += 1
    print(f"[B] witness calibration (35): depth1 {dict(wsp[1])}  depth2 {dict(wsp[2])}  "
          f"depth3 {dict(wsp[3])}   (O87 said depth3 {{4:32, 2:3}})")

    # ---- C. witness-overlap profiles + region lattice ----
    profs = Counter()
    valhist = Counter()
    for v in d17:
        T = Ts[v]
        prof = sorted(len(T & TS[u]) for u in m18)
        profs[tuple(sorted(Counter(prof).items()))] += 1
        valhist.update(prof)
    print(f"[C] |T n T_S| value histogram over 1344x35: {dict(sorted(valhist.items()))}")
    print(f"[C] distinct per-element profile signatures: {len(profs)}")
    for sig, n in profs.most_common(12):
        print(f"      {dict(sig)}  x{n}")

    # region-lattice atoms on H across the 35 T_S
    memb = {}
    for i in range(32):
        memb.setdefault(tuple(i in TS[u] for u in m18), []).append(i)
    atomsH = sorted(len(v) for v in memb.values())
    # atoms on G across the 35 S
    membG = {}
    for z in range(16):
        membG.setdefault(tuple(z in Ssets[u] for u in m18), []).append(z)
    atomsG = {tuple(sorted(v)): sum(k) for k, v in
              ((tuple(k), v) for k, v in membG.items())}
    zcount = Counter()
    for u in m18:
        zcount.update(Ssets[u])
    print(f"[C] region-lattice atoms on H (35 T_S): {len(memb)} atoms, sizes {atomsH}")
    print(f"[C] region-lattice atoms on G (35 S): {len(membG)} atoms, "
          f"sizes {sorted(len(v) for v in membG.values())}")
    print(f"[C] per-z membership count (of 35 S's): {dict(sorted(Counter(zcount.values()).items()))} "
          f"-> z-degrees {sorted(zcount.values(), reverse=True)}")
    pairS = Counter(len(Ssets[a] & Ssets[b]) for a, b in combinations(m18, 2))
    print(f"[C] pairwise |S n S'| over C(35,2): {dict(sorted(pairS.items()))}")

    # ---- D. descent anatomy ----
    v2 = [(pow(z, 9, P) + lam * pow(z, 8, P)) % P for z in G]
    pat = Counter()
    recs = []
    for v in d17:
        T = Ts[v]
        B, O, Z, sig = [], [], [], {}
        for z in range(16):
            a, b = z in T, (z + 16) in T
            if a and b: B.append(z)
            elif a or b:
                O.append(z); sig[z] = +1 if a else -1
            else: Z.append(z)
        pat[(len(B), len(O))] += 1
        cs = coeffs[v]
        ce, co = cs[0::2], cs[1::2]
        # forced forms (only meaningful at |B|=7)
        rec = dict(v=v, B=frozenset(B), O=frozenset(O), sig=tuple(sig[z] for z in sorted(O)))
        if len(B) == 7:
            PiB = [1]
            for z in B:
                PiB = polymul(PiB, [(-G[z]) % P, 1])
            gamma = co[7]
            assert gamma != 0 and all(co[d] == gamma * PiB[d] % P for d in range(8)), \
                "c_o != gamma*Pi_B"
            IB = lagrange([(G[z], v2[z]) for z in B]) + [0]
            alpha = ce[7]
            assert all(ce[d] == (IB[d] + alpha * PiB[d]) % P for d in range(8)), \
                "c_e != I_B(v2) + alpha*Pi_B"
            rec.update(alpha=alpha, gamma=gamma)
        recs.append(rec)
    print(f"[D] fiber pattern (|B|,|O|) histogram: {dict(sorted(pat.items()))}  "
          f"(2|B|+|O| = 17 check: {all(2*a+b == 17 for a, b in pat)})")
    Bcount = Counter(r['B'] for r in recs)
    print(f"[D] distinct B-sets: {len(Bcount)}; per-B multiplicity histogram "
          f"{dict(sorted(Counter(Bcount.values()).items()))}")
    # B vs the 35 witness S-sets
    Bsets = sorted(Bcount, key=lambda b: tuple(sorted(b)))
    inS = Counter()
    maxint = Counter()
    for b in Bcount:
        ns = sum(1 for u in m18 if b <= Ssets[u])
        inS[ns] += 1
        maxint[max(len(b & Ssets[u]) for u in m18)] += 1
    print(f"[D] #witness-S's containing B (per distinct B): {dict(sorted(inS.items()))}")
    print(f"[D] max |B n S| per distinct B: {dict(sorted(maxint.items()))}")
    # per-B: which (O, sigma) appear; O inside which region?
    osig = Counter()
    OmS = Counter()
    for r in recs:
        b = r['B']
        wit_with_B = [u for u in m18 if b <= Ssets[u]]
        unionS = frozenset().union(*[Ssets[u] for u in wit_with_B]) if wit_with_B else frozenset()
        OmS[(len(r['O'] & unionS), len(r['O']))] += 1
        osig[(len(set(r['O'])), r['sig'].count(1))] += 1
    print(f"[D] |O| and +signs histogram (|O|, #plus): {dict(sorted(osig.items()))}")
    print(f"[D] O inside union of S's containing B (|O n unionS|, |O|): {dict(sorted(OmS.items()))}")
    # per-B count of distinct (O,sig)
    perB = Counter()
    for r in recs:
        perB[r['B']] += 1
    print(f"[D] per-B element counts (sample of distribution): "
          f"{dict(sorted(Counter(perB.values()).items()))}")
    # gamma pairing under negation (negation: c(-x): gamma -> -gamma, alpha -> alpha)
    # ---- E. negation orbits ----
    s17 = set(d17)
    fixed = 0; paired = 0
    for v in d17:
        vn = tuple(v[(i + 16) % 32] for i in range(32))
        assert vn in s17, "negation does not act!"
        if vn == v: fixed += 1
        else: paired += 1
    print(f"[E] negation x->-x acts on the 1344: fixed {fixed}, in 2-orbits {paired} "
          f"-> orbits: {fixed + paired // 2} ({paired // 2} free pairs)")
    # does negation preserve B and flip sigma?
    r0 = recs[0]
    vn = tuple(r0['v'][(i + 16) % 32] for i in range(32))
    rn = next(r for r in recs if r['v'] == vn)
    print(f"[E] sample negation pair: B equal {r0['B'] == rn['B']}, O equal {r0['O'] == rn['O']}, "
          f"sigma flipped {tuple(-s for s in r0['sig']) == rn['sig']}, "
          f"alpha equal {r0.get('alpha') == rn.get('alpha')}, "
          f"gamma negated {(r0.get('gamma', 0) + rn.get('gamma', 0)) % P == 0}")
    return dict(w=w, d17=d17, m18=m18, recs=recs, Ssets=Ssets, TS=TS, Bcount=Bcount)

res_c = anatomize("CANONICAL", LAM, "my17_*.txt", "my18_*.txt")
res_a = anatomize("ALT(second tie value)", LAM_ALT, "myalt17_*.txt", "myalt18_*.txt")

# ---- rotation transport canonical -> alt: x -> h32^4 x maps w_lam to scalar * w_{lam*h32^-8} ----
print(f"\n{'='*78}\n== ROTATION TRANSPORT (tie-class equivariance)\n{'='*78}")
j = 4
s = pow(h32, (-18 * j) % 32, P)
assert LAM * pow(h32, (-2 * j) % 32, P) % P == LAM_ALT % P
img17 = {tuple(s * v[(i + j) % 32] % P for i in range(32)) for v in res_c['d17']}
img18 = {tuple(s * v[(i + j) % 32] % P for i in range(32)) for v in res_c['m18']}
print(f"transport x->h32^{j} x, scalar h32^{(-18*j) % 32}: "
      f"1344-layer maps ONTO alt 1344: {img17 == set(res_a['d17'])}; "
      f"35 maps onto alt 35: {img18 == set(res_a['m18'])}")
print("\nDONE")
