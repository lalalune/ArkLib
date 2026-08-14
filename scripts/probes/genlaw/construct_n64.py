"""FORECAST VERIFIER, part 3: constructive mod-p spot verification at n=64.

p = BabyBear = 15*2^27+1 (64 | 2^27 so mu_64 splits), g0 = 31, H = mu_64,
w = X^34 + lam*X^32, lam = -z*, z* = g0^((p-1)/4) = H[16].
For a stratified sample of >=200 enumerated (B,O,sigma) solutions (both global
signs): build e = Prod_{b in B}(X^2 - z_b)(X-x1)(X-x2)(X-x3)(X-xi), xi = -sum x_i;
verify e is monic deg 34 with coeff[33]=0 and coeff[32]=lam (so c = w - e has
deg < 32, a genuine codeword), and that c agrees with w on EXACTLY 33 points =
the predicted T. Then 50 random NON-solutions must fail (coeff[32] != lam)."""
import json, random
from itertools import combinations

P = 15 * (1 << 27) + 1
g0 = 31
n, s = 64, 32
h = pow(g0, (P - 1) // n, P)
H = [pow(h, i, P) for i in range(n)]
G = [H[(2 * z) % n] for z in range(s)]
ZS = pow(g0, (P - 1) // 4, P)
assert ZS == H[16] == G[8]
LAM = (P - ZS) % P
w = [(pow(x, 34, P) + LAM * pow(x, 32, P)) % P for x in H]
print(f"p = {P}, h64 = {h}, z* = {ZS}, lam = {LAM}")

sols = [(frozenset(B), tuple(O), tuple(sg))
        for B, O, sg in json.load(open("/tmp/genlaw/n64_sols.json"))]
solset = set(sols)
cl = json.load(open("/tmp/genlaw/n64_class_records.json"))
strat_of = {(tuple(c['O']), tuple(c['sig'])): (c['h'], c['v'], c['k']) for c in cl}

random.seed(20260610)
# stratified sample: 25 classes per (h,v,k) stratum (or all if fewer)
by_strat = {}
for B, O, sg in sols:
    by_strat.setdefault(strat_of[(O, sg)], []).append((B, O, sg))
sample = []
for st, lst in sorted(by_strat.items()):
    sample += random.sample(lst, min(25, len(lst)))
print(f"sampled {len(sample)} (B,O,sigma) solutions across strata "
      f"{sorted(by_strat)} -> x2 signs = {2 * len(sample)} elements")

def poly_e(B, O, dvec):
    X = [H[O[i] + s * dvec[i]] for i in range(3)]
    xi = (-sum(X)) % P
    e = [1]
    for b in sorted(B):
        zb = G[b]
        ne = [0] * (len(e) + 2)
        for t, c in enumerate(e):
            ne[t + 2] = (ne[t + 2] + c) % P
            ne[t] = (ne[t] - c * zb) % P
        e = ne
    for r in X + [xi]:
        ne = [0] * (len(e) + 1)
        for t, c in enumerate(e):
            ne[t + 1] = (ne[t + 1] + c) % P
            ne[t] = (ne[t] - c * r) % P
        e = ne
    return e, X, xi

def evals(coeffs, x):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % P
    return acc

ok_n = 0
distinct = set()
for B, O, sg in sample:
    for flip in (0, 1):
        dvec = tuple((flip + d) % 2 for d in (0, sg[0], sg[1]))
        e, X, xi = poly_e(B, O, dvec)
        assert len(e) == 35 and e[34] == 1, "not monic deg 34"
        assert e[33] == 0, "X^33 coeff nonzero (xi convention broken)"
        assert e[32] == LAM, "consistency FAILS mod p for an enumerated solution!"
        assert xi not in set(H) and xi != 0, "L4 fails: xi in mu_64 u {0} mod p"
        # c = w - e: degree < 32 codeword; agreement set = zeros of e on H
        Tpred = sorted([b for b in B] + [b + s for b in B]
                       + [O[i] + s * dvec[i] for i in range(3)])
        zeros = [i for i in range(n) if evals(e, H[i]) == 0]
        assert zeros == Tpred and len(zeros) == 33, \
            f"agreement set wrong: {len(zeros)} points"
        cvec = tuple((w[i] - evals(e, H[i])) % P for i in range(n))
        distinct.add(cvec)
        ok_n += 1
print(f"[CONSTRUCT] {ok_n} elements built and verified: monic deg-34 e, "
      f"coeff(X^33)=0, coeff(X^32)=lam -> c = w - e is a genuine deg<32 codeword;")
print(f"            agreement with w EXACTLY 33 points, equal to predicted T; "
      f"xi outside mu_64 u {{0}} for all; {len(distinct)} distinct codewords.")

# ---- 50 random NON-solutions must fail --------------------------------------------
SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
fails, tried = 0, 0
nons = []
while len(nons) < 50:
    O = tuple(sorted(random.sample(range(s), 3)))
    sg = random.choice(SIGS)
    rest = [z for z in range(s) if z not in O]
    B = frozenset(random.sample(rest, 15))
    if (B, O, sg) in solset:
        continue
    nons.append((B, O, sg))
for B, O, sg in nons:
    dvec = (0, sg[0], sg[1])
    e, X, xi = poly_e(B, O, dvec)
    # failure mode: e[32] != LAM  (then w - e has degree exactly 32: NOT a codeword)
    if e[32] != LAM:
        fails += 1
    else:
        print(f"  !! non-solution PASSED mod p (spurious): B={sorted(B)} O={O} sg={sg}")
print(f"[NEGATIVE] {fails}/50 random non-solutions correctly FAIL the deg<32 "
      f"condition mod p (e coeff X^32 != lam).")
assert fails == 50
print("CONSTRUCTIVE N64 CHECK DONE: all positive and negative checks PASSED")
