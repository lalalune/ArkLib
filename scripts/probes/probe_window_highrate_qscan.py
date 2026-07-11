#!/usr/bin/env python3
"""HIGH-RATE window q-scan + k-push (#371 WB lane, Fable round 4, part 2).

Follow-up to probe_window_highrate_redteam.py which found doubly-WB-solvable stacks
with 4 bad scalars at (17,8,3,2)/(11,10,5,2) and 5 = w+3 bad at (13,12,7,2).

Pre-registered questions:
  Q1 (k-push): at (17,16,11,2) (mu_16 = F_17^*, sigma=0, j=0), do doubly-rational
      stacks exceed w+3 = 5 bad scalars?  YES would REFUTE WindowRationalBounded.
  Q2 (q-scan): at fixed (n,k,w) = (12,7,2) and (8,3,2), does the max bad count DECAY
      as q grows ((q,12): 13,37,61,97; (q,8): 17,41,73,89)?  Decay = the surplus is
      ARITHMETIC (small-field coincidences; census-layer), so a production-budget
      version of the below-UDR law survives with a q-threshold.
"""
import random
from itertools import combinations

random.seed(371)

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        xs = {pow(x, i, q) for i in range(n)}
        if len(xs) == n: return x
    return None

def make_tools(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def solve(idxs, vals):
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m = len(rows); r = 0; piv_cols = []
        for c in range(k):
            piv = next((i for i in range(r, m) if rows[i][c] % q), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [(v * inv) % q for v in rows[r]]
            for i in range(m):
                if i != r and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
            piv_cols.append(c); r += 1
        if any(rows[i][k] % q for i in range(r, m)): return None
        co = [0] * k
        for ri, c in enumerate(piv_cols): co[c] = rows[ri][k]
        return co
    def evalpoly(co, x):
        a = 0
        for cf in reversed(co): a = (a * x + cf) % q
        return a
    return solve, evalpoly

def bad_count(q, n, k, w, dom, u0, u1, solve, evalpoly, want_detail=False):
    tmin = n - w
    bads = []
    subs = list(combinations(range(n), tmin))
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        expl = None
        for S in subs:
            co = solve(list(S), line)
            if co is not None:
                A = [i for i in range(n) if evalpoly(co, dom[i]) == line[i]]
                if len(A) >= tmin: expl = (co, A); break
        if expl is None: continue
        co, A = expl
        if solve(A, u0) is None or solve(A, u1) is None:
            bads.append((gam, tuple(co), tuple(A)))
    return bads

def ratword(q, dom, l, r):
    out = []
    for x in dom:
        lv = 0
        for cf in reversed(l): lv = (lv * x + cf) % q
        if lv == 0: return None
        rv = 0
        for cf in reversed(r): rv = (rv * x + cf) % q
        out.append(rv * pow(lv, q - 2, q) % q)
    return tuple(out)

def wbsolv(q, n, k, w, dom, u):
    rows = []
    for i in range(n):
        x = dom[i]
        row = [(pow(x, j, q) * u[i]) % q for j in range(w + 1)]
        row += [(-pow(x, j, q)) % q for j in range(w + k)]
        rows.append(row)
    m = len(rows); cols = 2 * w + k + 1; r = 0
    for c in range(cols):
        piv = next((i for i in range(r, m) if rows[i][c] % q), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], q - 2, q)
        rows[r] = [(v * inv) % q for v in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] % q:
                f = rows[i][c]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r < cols

def search(q, n, k, w, NS_rand, NS_climb, label):
    g = find_gen(q, n)
    if g is None:
        print(f"[{label}] no mu_{n} in F_{q}"); return None
    dom = [pow(g, i, q) for i in range(n)]
    solve, evalpoly = make_tools(q, n, k, dom)
    best = (0, None)
    for _ in range(NS_rand):
        l0 = [random.randrange(q) for _ in range(w + 1)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        u0 = ratword(q, dom, l0, r0); u1 = ratword(q, dom, l1, r1)
        if u0 is None or u1 is None: continue
        b = bad_count(q, n, k, w, dom, u0, u1, solve, evalpoly)
        if len(b) > best[0]: best = (len(b), (u0, u1))
    if best[1]:
        u0, u1 = list(best[1][0]), list(best[1][1])
        cur = best[0]
        for _ in range(NS_climb):
            i = random.randrange(n); which = random.randrange(2)
            old0, old1 = u0[i], u1[i]
            if which == 0: u0[i] = random.randrange(q)
            else: u1[i] = random.randrange(q)
            b = bad_count(q, n, k, w, dom, tuple(u0), tuple(u1), solve, evalpoly)
            if len(b) >= cur: cur = len(b)
            else: u0[i], u1[i] = old0, old1
        s0 = wbsolv(q, n, k, w, dom, u0); s1 = wbsolv(q, n, k, w, dom, u1)
        b = bad_count(q, n, k, w, dom, tuple(u0), tuple(u1), solve, evalpoly)
        tag = "PROP-RELEVANT" if (s0 and s1) else "outside Prop"
        print(f"[{label}] rand-max={best[0]}  climbed={len(b)}  ({tag})  w+3={w+3}")
        if len(b) > w + 3 and s0 and s1:
            print("  !!! VIOLATION: WindowRationalBounded REFUTED at this instance !!!")
            print("  u0 =", tuple(u0)); print("  u1 =", tuple(u1))
            for gam, co, A in b: print(f"    gamma={gam} P={co} |A|={len(A)}")
        return len(b) if (s0 and s1) else best[0]
    print(f"[{label}] nothing found")
    return 0

print("== Q1: k-push at (17,16,11,2) ==")
search(17, 16, 11, 2, 400, 800, "(17,16,11,2)")

print("== Q2: q-scan at (n,k,w)=(12,7,2) ==")
for q in (13, 37, 61, 97):
    search(q, 12, 7, 2, 500, 600, f"({q},12,7,2)")

print("== Q2b: q-scan at (n,k,w)=(8,3,2) ==")
for q in (17, 41, 73, 89):
    search(q, 8, 3, 2, 800, 600, f"({q},8,3,2)")
