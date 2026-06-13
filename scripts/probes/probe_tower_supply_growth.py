#!/usr/bin/env python3
"""#389 DECISIVE: sub-Johnson line-list growth on 2-power tower domains mu_{2^mu}.

Does the max sub-Johnson list (k=2 lines) on mu_n grow POLYNOMIALLY or
EXPONENTIALLY as n climbs the tower? This decides whether the supply wall is
closeable on the PRIZE domains (n=2^mu). k=2 (lines a+bx), agreement counted by
direct line enumeration (C(n,2) lines), fast at every scale. Sub-Johnson target
agreement t = round(0.75*sqrt(2n)) (Johnson agreement = sqrt(k*n)=sqrt(2n)),
clamped >= 3. Adversarially hill-climb the word from random + tower-fiber seeds.
"""
import sys, math, random
from itertools import combinations
random.seed(389)

def field_prime(n):
    p = max(257, n + 1)
    while True:
        if (p - 1) % n == 0 and all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += 1

def subgroup(p, n):
    m = p - 1; fac = set(); d = 2; mm = m
    while d*d <= mm:
        if mm % d == 0:
            fac.add(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    g = next(g for g in range(2, p) if all(pow(g, m//q, p) != 1 for q in fac))
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, i, p) for i in range(n)})

def line_list(dom, w, p, t):
    """max agreement over all lines, and #lines with agreement >= t."""
    n = len(dom)
    seen = {}
    for i, j in combinations(range(n), 2):
        xi, xj = dom[i], dom[j]
        # b = (w_j - w_i)/(x_j - x_i), a = w_i - b x_i
        b = ((w[j] - w[i]) * pow(xj - xi, p-2, p)) % p
        a = (w[i] - b*xi) % p
        if (a, b) in seen: continue
        agr = sum(1 for l in range(n) if (a + b*dom[l]) % p == w[l])
        seen[(a, b)] = agr
    cnt = sum(1 for agr in seen.values() if agr >= t)
    return cnt, (max(seen.values()) if seen else 0)

def fiber_seed(dom, p, depth):
    img = sorted({pow(x, 2**depth, p) for x in dom})
    W = {y: random.randrange(p) for y in img}
    return [W[pow(x, 2**depth, p)] for x in dom]

def hill(dom, p, t, iters, seeds):
    n = len(dom); best = 0
    starts = list(seeds) + [[random.randrange(p) for _ in range(n)] for _ in range(3)]
    for w0 in starts:
        w = list(w0); cur = line_list(dom, w, p, t)[0]
        for _ in range(iters):
            i = random.randrange(n); old = w[i]
            w[i] = random.randrange(p)
            new = line_list(dom, w, p, t)[0]
            if new >= cur: cur = new
            else: w[i] = old
        best = max(best, cur)
    return best

print("mu  n    p     t  frac  Johnson  maxlist  log2/log2n", flush=True)
rows = []
for mu in (3, 4, 5, 6):
    n = 1 << mu
    p = field_prime(n)
    dom = subgroup(p, n)
    johnson = math.sqrt(2*n)
    t = max(3, round(0.75*johnson))
    seeds = [fiber_seed(dom, p, j) for j in range(1, mu)]
    ml = hill(dom, p, t, 300, seeds)
    ratio = math.log2(max(ml,1)) / math.log2(n)
    rows.append((mu, n, ml, ratio))
    print(f"{mu}  {n:3d}  {p:5d}  {t}  {t/n:.3f}  {johnson/n:.3f}  {ml:4d}     {ratio:.2f}",
          flush=True)
print(flush=True)
print("log2(maxlist)/log2(n) ~ const  => POLYNOMIAL supply  => wall closeable on towers",
      flush=True)
print("ratio growing with mu          => super-polynomial    => wall genuine", flush=True)
print(f"ratios: {[round(r[3],2) for r in rows]}", flush=True)
