#!/usr/bin/env python3
"""#389 LINEAR-LAW REGIME PROBE (scratch).

Decisive question: the capped per-word supply optimum  S*(n) = max_w  sum_{lines L:
t <= a_L <= cap} C(a_L, t)  over function graphs w: dom -> F_q (k=2, lines).
The census measured S*(n) ~ linear at q=31, n<=24 (n/q <= 0.77).  Is it linear
because of RS structure (then it stays linear as n->q AND in the sparse
production regime n<<q), or only an artifact of small n?

We measure S*(n) by multi-restart hill-climb in two regimes:
  (A) DENSE: q fixed (31, 61), n -> q.   Does S*/n blow up near n~q?
  (B) SPARSE: q >> n (q=127,1009,10007), fixed small n.  Is S* SMALLER /
      more constrained (the production-relevant regime)?
Also extracts the extremal configuration: #rich lines L_count, incidences
I=sum a_L, mean pencil degree I/n, max pencil degree, line-size histogram.
"""
import random, math
from itertools import combinations

def comb(a, t):
    return math.comb(a, t) if a >= t else 0

def supply(w, dom, q, t, cap):
    """capped supply = sum over lines with t<=a_L<=cap of C(a_L,t);
    also returns (L_count rich+capped, total incidences I, max pencil deg,
    size histogram)."""
    n = len(dom)
    # build lines: dict (a,b)->set of point indices. enumerate pairs.
    lines = {}
    for i, j in combinations(range(n), 2):
        xi, xj = dom[i], dom[j]
        dx = (xj - xi) % q
        a = ((w[j] - w[i]) * pow(dx, q - 2, q)) % q
        b = (w[i] - a * xi) % q
        key = (a, b)
        s = lines.get(key)
        if s is None:
            lines[key] = {i, j}
        else:
            s.add(i); s.add(j)
    S = 0
    Lc = 0
    I = 0
    deg = [0] * n
    hist = {}
    for key, s in lines.items():
        aL = len(s)
        if t <= aL <= cap:
            S += comb(aL, t)
            Lc += 1
            I += aL
            hist[aL] = hist.get(aL, 0) + 1
            for i in s:
                deg[i] += 1
    return S, Lc, I, (max(deg) if deg else 0), hist

def hillclimb(dom, q, t, cap, iters, restarts, seed):
    rnd = random.Random(seed)
    n = len(dom)
    best = -1
    best_info = None
    for r in range(restarts):
        w = [rnd.randrange(q) for _ in range(n)]
        cur, *_ = supply(w, dom, q, t, cap)
        stale = 0
        for it in range(iters):
            i = rnd.randrange(n)
            old = w[i]
            w[i] = rnd.randrange(q)
            nv, *info = supply(w, dom, q, t, cap)
            if nv >= cur:
                if nv > cur:
                    stale = 0
                cur = nv
            else:
                w[i] = old
                stale += 1
            if stale > 4 * n:
                break
        val, Lc, I, mx, hist = supply(w, dom, q, t, cap)
        if val > best:
            best = val
            best_info = (Lc, I, round(I / n, 2), mx, dict(sorted(hist.items())))
    return best, best_info

def run(label, q, n, k=2, m=1, iters=400, restarts=8, seed=0):
    t = k + m + 1          # core size = 4
    cap = 2 * k + m + 1    # agreement cap = 6
    dom = list(range(n))   # {0,...,n-1} subset of F_q  (n<=q)
    S, info = hillclimb(dom, q, t, cap, iters, restarts, seed)
    Lc, I, meandeg, mx, hist = info
    print(f"{label:9s} q={q:6d} n={n:3d} n/q={n/q:5.3f} | S*={S:5d}  "
          f"S*/n={S/n:5.2f}  Lc={Lc:4d} Lc/n={Lc/n:4.2f}  meandeg={meandeg:4.1f} "
          f"maxdeg={mx:2d}  hist={hist}")
    return S

print(__doc__)
print("t=4 (core), cap=6 (agreement);  partition value ~ (n/cap)*C(cap,t) = (n/6)*15 = 2.5n")
print("\n(A) DENSE regime: q fixed, n -> q  -- does S*/n blow up near capacity?")
for q in (31, 61):
    for n in range(12, q + 1, 4 if q == 31 else 8):
        run(f"dense", q, n, iters=500, restarts=10, seed=1)
    print()

print("(B) SPARSE regime (production-shaped n<<q): fixed n, q growing")
for n in (16, 24):
    for q in (31, 61, 127, 1009, 10007):
        if q <= n:
            continue
        run(f"sparse", q, n, iters=500, restarts=10, seed=2)
    print()
