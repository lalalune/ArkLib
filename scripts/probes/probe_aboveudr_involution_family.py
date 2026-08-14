#!/usr/bin/env python3
"""ABOVE-UDR test of the involution-alignment family: does MCA separate from CA?

(#371 WB lane, Fable round 4, part 3.)  Below UDR the normalizer-pair family gives
(n-2)/2 bad scalars (WindowRationalBounded refuted).  ABOVE UDR the kernel freedom
j = 3w+k-1-n >= (n-k)/2 is huge, so per-(T,gamma) alignment is easy and the
EXPLAINABLE count explodes; the entire question is the no-joint clause (which is no
longer free).  Pre-registered question:

  For involution-structured stacks (l = product of w/2 involution quadratics, R built
  by alignment) at w = UDR+1, UDR+2, ..., how many gamma are (a) line-explainable,
  (b) genuinely mca-bad (no joint pair on the full agreement set of some witness)?

  (b) >> n at some w < Johnson would be a bad-side breakthrough toward pinning
  delta* at/below that radius for MCA (separation from CA).  (b) collapsing to
  O(n) while (a) explodes = the no-joint clause is doing real work above UDR --
  structural support for MCA ~ CA there.

Method: exact, no sampling.  For each gamma: explainability = exists S (n-w subset)
with line|_S in RS_k|_S (rank test); badness = exists explainer c (enumerate via all
(n-w)-subsets, dedup agreement sets A) with no joint pair on A.
NOTE above UDR explainers are NOT unique; we enumerate distinct agreement sets.
"""
from itertools import combinations
import random

random.seed(371371)

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if len({pow(x, i, q) for i in range(n)}) == n: return x
    return None

def make_solver(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def solve(idxs, vals):
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m_, r, piv_cols = len(rows), 0, []
        for c in range(k):
            piv = next((i for i in range(r, m_) if rows[i][c] % q), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [(v * inv) % q for v in rows[r]]
            for i in range(m_):
                if i != r and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
            piv_cols.append(c); r += 1
        if any(rows[i][k] % q for i in range(r, m_)): return None
        co = [0] * k
        for ri, c in enumerate(piv_cols): co[c] = rows[ri][k]
        return co
    return solve

def evalp(co, x, q):
    a = 0
    for cf in reversed(co): a = (a * x + cf) % q
    return a

def analyze(q, n, k, w, dom, u0, u1, solve, label):
    tmin = n - w
    subs = list(combinations(range(n), tmin))
    expl_g, bad_g = [], []
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        agreement_sets = set()
        explainable = False
        for S in subs:
            co = solve(list(S), line)
            if co is None: continue
            explainable = True
            A = tuple(i for i in range(n) if evalp(co, dom[i], q) == line[i])
            agreement_sets.add(A)
        if not explainable: continue
        expl_g.append(gam)
        isbad = False
        for A in agreement_sets:
            if solve(list(A), u0) is None or solve(list(A), u1) is None:
                isbad = True; break
        if isbad: bad_g.append(gam)
    print(f"[{label}] (q,n,k,w)=({q},{n},{k},{w}) UDR={(n-k)//2} "
          f"explainable={len(expl_g)} BAD={len(bad_g)} (q={q})")
    return expl_g, bad_g

def involution_stack(q, n, k, w, dom, c=1):
    # l0, l1 = products of w/2 involution quadratics (roots off domain);
    # R0, R1 = random of degree <= w+k-1 -- alignment is NOT hand-tuned here:
    # above UDR the h-freedom does the aligning; we test both random-R and
    # T0-aligned-R variants.
    domset = set(dom)
    used = set()
    def next_root(avoid):
        for x in range(2, q):
            cx = c * pow(x, q - 2, q) % q
            if x in domset or cx in domset or cx == x or x in avoid or cx in avoid:
                continue
            return x, cx
        return None
    quads = []
    for _ in range(w):  # gather plenty; first w/2 for l0, next w/2 for l1
        r = next_root(used)
        if r is None: return None
        used |= set(r); quads.append(r)
    if len(quads) < w: return None
    def quadprod(qs):
        co = [1]
        for (a, b) in qs:
            co2 = [a * b % q, (-(a + b)) % q, 1]
            res = [0] * (len(co) + 2)
            for i, ai in enumerate(co):
                for j, bj in enumerate(co2):
                    res[i + j] = (res[i + j] + ai * bj) % q
            co = res
        return co
    l0 = quadprod(quads[: w // 2])
    l1 = quadprod(quads[w // 2: w])
    R0 = [random.randrange(q) for _ in range(w)]      # deg <= w-1 (structured small)
    R1 = [random.randrange(q) for _ in range(w)]
    def ratword(l, r):
        out = []
        for x in dom:
            lv = evalp(l, x, q)
            if lv == 0: return None
            out.append(evalp(r, x, q) * pow(lv, q - 2, q) % q)
        return tuple(out)
    return ratword(l0, R0), ratword(l1, R1)

INSTANCES = [
    # (q, n, k): UDR=(n-k)/2; test w = UDR+1 .. UDR+2 (above UDR, below Johnson-ish)
    (37, 12, 2),   # UDR=5: w=6,7  (Johnson ~ 12(1-sqrt(1/6)) ~ 7.1)
    (29, 14, 2),   # UDR=6: w=7    (n=14=2*7; q=29)
    (17, 8, 2),    # UDR=3: w=4    (production rate 1/4; compare HalfPairSliceExact n=8)
]

for (q, n, k) in INSTANCES:
    g = find_gen(q, n)
    if g is None:
        print(f"({q},{n},{k}): no domain"); continue
    dom = [pow(g, i, q) for i in range(n)]
    solve = make_solver(q, n, k, dom)
    udr = (n - k) // 2
    for w in (udr + 1, udr + 2):
        if w >= n - 1: continue
        best_bad = 0
        for trial in range(6):
            st = involution_stack(q, n, k, w, dom)
            if st is None or st[0] is None or st[1] is None: continue
            u0, u1 = st
            eg, bg = analyze(q, n, k, w, dom, u0, u1, solve,
                             f"invol trial {trial}")
            best_bad = max(best_bad, len(bg))
        # baseline: random rational stacks of full degree
        st = involution_stack(q, n, k, w, dom)
        print(f"  ==> ({q},{n},{k},{w}): best involution-family BAD = {best_bad}, "
              f"n = {n}, q = {q}")
