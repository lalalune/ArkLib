#!/usr/bin/env python3
"""#389 THE DIVISOR-POVERTY HYPOTHESIS, first falsifier: window-interior list sizes
are governed by the domain's divisor lattice.

Frame: the only known explosion mechanism on smooth domains is the divisor tower
(KKH26's capacity - Theta(1/log n) ceiling = tower depth log n). Prediction: at
matched (q, n, k, t-fraction), max window-interior list sizes order by divisor
richness; prime-order domains (no proper subtower) should show NO structured
window explosions -- their max lists should hug the generic/orchard level.

Test: F_1361 (1361 prime, 1360 = 16*85 = 2^4*5*17) contains mu_16 (2-power,
divisor-rich tower 16-8-4-2) and mu_17 (PRIME order, no proper subgroup).
Matched sizes 16 vs 17, same field, same k = 3.

  (P1) tower seeds on mu_16: fiber words w = W(x^2) carry lifted lists
       {g(x^2) : deg g <= 1} with doubled agreement -- count exact list sizes
       at t = 4, 6 for random W; record the tower floor.
  (P2) mu_17: verify no analog exists (only subgroup {1}); hill-climb max list
       at the matched fractions with the same budget as (P3).
  (P3) mu_16 hill-climb with identical budget, started from random words
       AND from tower seeds.
Report: max list sizes side by side. PREDICTION: mu_16 >> mu_17 at matched t/n.
"""
import random
random.seed(389)

q = 1361
# generator of F_q^*: find primitive root
def is_primitive(g):
    for p in (2, 5, 17):
        if pow(g, (q - 1) // p, q) == 1:
            return False
    return True
g0 = next(g for g in range(2, q) if is_primitive(g))
mu16 = sorted(pow(g0, (q - 1) // 16 * i, q) for i in range(16))
mu17 = sorted(pow(g0, (q - 1) // 17 * i, q) for i in range(17))
assert len(set(mu16)) == 16 and len(set(mu17)) == 17

k = 3  # degree < 3 (quadratics)

def list_size(dom, w, t):
    """#codewords (deg<k) agreeing with w on >= t points: enumerate via
    interpolation through k-subsets (every codeword with >= t >= k agreements
    is determined by interpolation through any k of its agreement points)."""
    n = len(dom)
    pts = list(zip(dom, w))
    seen = {}
    from itertools import combinations
    for idx in combinations(range(n), k):
        xs = [dom[i] for i in idx]
        ys = [w[i] for i in idx]
        # Lagrange interpolation -> coefficient tuple
        coef = [0] * k
        for j in range(k):
            num = [1]
            den = 1
            for l in range(k):
                if l == j:
                    continue
                num = [(a * (-xs[l])) % q for a in num] + [0]
                for a in range(len(num) - 1):
                    num[a] = (num[a] + ([1] + [0] * 10)[0] * 0) % q
                # polynomial multiply (x - xs[l]) properly:
            # simpler: solve 3x3 Vandermonde directly
        # do direct Vandermonde solve instead
        a, b, c = xs
        ya, yb, yc = ys
        # f(x) = A + Bx + Cx^2 through (a,ya),(b,yb),(c,yc)
        det = ((b - a) * (c - a) * (c - b)) % q
        if det == 0:
            continue
        # Lagrange evaluation-free: compute coefficients
        inv = pow(det, q - 2, q)
        # standard divided differences
        d1 = ((yb - ya) * pow(b - a, q - 2, q)) % q
        d2 = ((yc - yb) * pow(c - b, q - 2, q)) % q
        C = ((d2 - d1) * pow(c - a, q - 2, q)) % q
        B = (d1 - C * (a + b)) % q
        A = (ya - a * (B + C * a)) % q
        key = (A, B, C)
        if key in seen:
            continue
        agr = sum(1 for (x, y) in pts if (A + B * x + C * x * x) % q == y)
        seen[key] = agr
    return {key: agr for key, agr in seen.items()}

def max_list(dom, w, t):
    return sum(1 for agr in list_size(dom, w, t).values() if agr >= t)

# (P1) tower seeds on mu_16
mu8 = sorted(set((x * x) % q for x in mu16))
assert len(mu8) == 8
def tower_word():
    W = {y: random.randrange(q) for y in mu8}
    return [W[(x * x) % q] for x in mu16]

best16_seed = {4: 0, 5: 0, 6: 0}
for _ in range(40):
    w = tower_word()
    for t in (4, 5, 6):
        best16_seed[t] = max(best16_seed[t], max_list(mu16, w, t))
print(f"mu16 tower seeds: max list t=4: {best16_seed[4]}, t=5: {best16_seed[5]}, "
      f"t=6: {best16_seed[6]}")

# (P2)/(P3) hill-climb both domains, same budget
def hill_climb(dom, t, iters=900, restarts=6, seed_words=None):
    n = len(dom)
    best = 0
    starts = []
    if seed_words:
        starts.extend(seed_words)
    while len(starts) < restarts:
        starts.append([random.randrange(q) for _ in range(n)])
    for w0 in starts:
        w = list(w0)
        cur = max_list(dom, w, t)
        for _ in range(iters // restarts):
            i = random.randrange(n)
            old = w[i]
            # propose: align w[i] with a random near-miss codeword
            fam = list_size(dom, w, t)
            cands = [key for key, agr in fam.items() if agr == t - 1]
            if cands and random.random() < 0.8:
                A, B, C = random.choice(cands)
                x = dom[i]
                w[i] = (A + B * x + C * x * x) % q
            else:
                w[i] = random.randrange(q)
            new = max_list(dom, w, t)
            if new >= cur:
                cur = new
            else:
                w[i] = old
        best = max(best, cur)
    return best

for t16, t17 in ((4, 4), (5, 5), (6, 6)):
    b16 = hill_climb(mu16, t16, seed_words=[tower_word() for _ in range(3)])
    b17 = hill_climb(mu17, t17)
    f16, f17 = t16 / 16, t17 / 17
    print(f"t={t16}: mu16 max list = {b16} (frac {f16:.2f}) | "
          f"mu17 max list = {b17} (frac {f17:.2f})")
print("Johnson agreement ~ sqrt(k*n) = sqrt(48) ~ 6.93 (mu16), sqrt(51) ~ 7.14 (mu17)")
print("window-interior = t in {4,5,6}: PREDICTION mu16 >> mu17 if the tower frame holds")
