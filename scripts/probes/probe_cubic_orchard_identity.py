#!/usr/bin/env python3
"""Pre-registered probe (#389): THE CUBIC ORCHARD IDENTITY + extremality census.

Claim 1 (PROVEN in CubicOrchardIdentity.lean): for w = x^3 on ANY domain and the
k = 2 code, the number of codewords with agreement >= 3 equals the number of
3-subsets of the domain summing to 0 (collinearity on the cubic graph is exactly
zero-sum: (a-c)(a+b+c) = 0).

Claim 2 (exact list profile of the cubic family): a general cubic
c3*x^3 + c2*x^2 + c1*x + c0 (c3 != 0) has list size = #{triples T : sum T = -c2/c3},
so the best cubic word achieves max_s fiber(s) of the triple-sum distribution.

Claim 3 (extremality census, OPEN): is the best cubic fiber the global maximum
over ALL words?  Hill-climb comparison at small smooth instances.

Reference cap: Green-Tao orchard bound floor(n(n-3)/6) + 1 (real plane).
"""
import itertools, random

def smooth_dom(q, n):
    # multiplicative subgroup of order n in F_q (requires n | q-1)
    assert (q - 1) % n == 0
    g = next(g for g in range(2, q) if all(
        pow(g, (q - 1) // p, q) != 1
        for p in set(_factor(q - 1))))
    w = pow(g, (q - 1) // n, q)
    return sorted(pow(w, i, q) for i in range(n))

def _factor(m):
    fs, d = [], 2
    while d * d <= m:
        while m % d == 0:
            fs.append(d); m //= d
        d += 1
    if m > 1:
        fs.append(m)
    return fs

def list_size(q, dom, word, k, a):
    # count deg<k codewords agreeing with word on >= a points (k=2: lines)
    n = len(dom)
    cnt = 0
    seen = set()
    for i, j in itertools.combinations(range(n), 2):
        x1, y1, x2, y2 = dom[i], word[i], dom[j], word[j]
        A = (y1 - y2) * pow(x1 - x2, q - 2, q) % q
        B = (y1 - A * x1) % q
        if (A, B) in seen:
            continue
        seen.add((A, B))
        agr = sum(1 for t in range(n) if (A * dom[t] + B) % q == word[t])
        if agr >= a:
            cnt += 1
    return cnt

def fiber_counts(q, dom):
    from collections import Counter
    c = Counter()
    for T in itertools.combinations(dom, 3):
        c[sum(T) % q] += 1
    return c

def hill_climb_max(q, dom, k, a, iters=4000, restarts=6, seed=389):
    rng = random.Random(seed)
    n = len(dom)
    best = 0
    for _ in range(restarts):
        w = [rng.randrange(q) for _ in range(n)]
        cur = list_size(q, dom, w, k, a)
        for _ in range(iters):
            i, v = rng.randrange(n), rng.randrange(q)
            old = w[i]; w[i] = v
            new = list_size(q, dom, w, k, a)
            if new >= cur:
                cur = new
            else:
                w[i] = old
        best = max(best, cur)
    return best

if __name__ == "__main__":
    for q, n in [(29, 14), (31, 15), (41, 20), (37, 18)]:
        dom = smooth_dom(q, n)
        cubic = [pow(x, 3, q) for x in dom]
        ls = list_size(q, dom, cubic, 2, 3)
        zs = sum(1 for T in itertools.combinations(dom, 3) if sum(T) % q == 0)
        fc = fiber_counts(q, dom)
        best_s, best_f = max(fc.items(), key=lambda kv: kv[1])
        gt = n * (n - 3) // 6 + 1
        print(f"q={q} n={n}: list(x^3,a>=3)={ls} zero-sum={zs} "
              f"IDENTITY={'OK' if ls == zs else 'FAIL'} | best cubic fiber: "
              f"s={best_s} count={best_f} | Green-Tao cap={gt}")
    # extremality census (small instances only; hill-climb is heuristic)
    for q, n in [(29, 14), (31, 15)]:
        dom = smooth_dom(q, n)
        fc = fiber_counts(q, dom)
        best_f = max(fc.values())
        hc = hill_climb_max(q, dom, 2, 3)
        print(f"q={q} n={n}: best cubic fiber={best_f} hill-climb global={hc} "
              f"cubic-extremal={'YES' if best_f >= hc else 'NO (gap '+str(hc-best_f)+')'}")
