"""Anatomy of the NEW r=5 stratum at s=32: pattern (b,r) = (14,5).
Collect all (B,O,mask) solutions of the balance law and chart:
parity profile, sigma-per-(B,O), B-multiplicity menu, L-axis strata,
event structure (which collisions make it feasible), eps split.
"""
from itertools import combinations
from math import comb
from collections import Counter, defaultdict

s, n, A = 32, 64, 16
r = 5
b = (s + 1 - r) // 2          # 14
Lfib = 3 * s // 4             # 48/2 = 24; exponent 48
pairs = list(combinations(range(r), 2))

sols = []
recs = []
for O in combinations(range(s), r):
    Oset = set(O)
    par = tuple(sorted(o % 2 for o in O))
    for m in range(1 << (r - 1)):
        a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
        cnt = [0] * n
        for (i, j) in pairs:
            cnt[(a[i] + a[j]) % n] += 1
        for o in O:
            cnt[(2 * o) % n] += 1
        cnt[(2 * Lfib) % n] += 1
        ok = True
        for mm in range(1, s, 2):
            if cnt[mm] != cnt[mm + s]:
                ok = False
                break
        if not ok:
            continue
        forced, freeax = [], []
        for c in range(A):
            d = cnt[2 * c] - cnt[(2 * c + s) % n]
            if abs(d) >= 2:
                ok = False
                break
            if d == -1:
                f = c
            elif d == 1:
                f = c + A
            else:
                if c not in Oset and (c + A) not in Oset:
                    freeax.append(c)
                continue
            if f in Oset:
                ok = False
                break
            forced.append(f)
        if not ok:
            continue
        h, v = len(forced), len(freeax)
        if (b - h) < 0 or (b - h) % 2 or (b - h) // 2 > v:
            continue
        k = (b - h) // 2
        recs.append((O, m, h, v, k, par))
        for pick in combinations(freeax, k):
            B = frozenset(forced) | set(pick) | {c + A for c in pick}
            sols.append((B, O, m))

print(f"r=5 (B,O,mask) classes: {len(sols)}  -> elements {2*len(sols)}")
assert len(sols) == 99512

par_hist = Counter(p for O, m, h, v, k, p in recs)
print("parity profiles of feasible (O,mask) classes:", dict(par_hist))
parc = Counter()
for B, O, m in sols:
    parc[tuple(sorted(o % 2 for o in O))] += 1
print("parity profiles weighted by completions:", dict(parc))

hvk = Counter((h, v, k) for O, m, h, v, k, p in recs)
print("(h,v,k) histogram over (O,mask) classes:", dict(sorted(hvk.items())))

# sigma multiplicity per (B,O)
BO = defaultdict(set)
for B, O, m in sols:
    BO[(B, O)].add(m)
sigm = Counter(len(v) for v in BO.values())
print("masks per (B,O):", dict(sigm))

# B multiplicity menu
Bc = Counter(B for B, O, m in sols)
print("distinct B:", len(Bc), " multiplicity hist:", dict(Counter(Bc.values())))

# eps for pure classes / mixed handling
def lax_strat(B, O, m):
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, r)]
    a = [O[i] + s * d[i] for i in range(r)]
    lo, hi = [], []
    def put(fib, tag):
        if fib == s // 4: lo.append(tag)
        elif fib == 3 * s // 4: hi.append(tag)
    for o in O: put(o, 'O')
    for (i, j) in pairs:
        e = (a[i] + a[j]) % n
        if e % 2 == 0: put((e // 2) % s, 'P')
    put(Lfib, 'L')
    for bb in B: put(bb, 'B')
    return '|'.join(sorted([''.join(sorted(lo)), ''.join(sorted(hi))]))

strat = Counter(lax_strat(*t) for t in sols)
print("z*-axis strata (classes):", dict(strat.most_common()))

# product-pairing structure: how do the 10 products balance? count antipodal
# product-product pairs (the new 'E5' event: x_i x_j = -x_k x_l)
def pp_events(O, m):
    d = [0] + [(m >> (i - 1)) & 1 for i in range(1, r)]
    a = [O[i] + s * d[i] for i in range(r)]
    pe = {(i, j): (a[i] + a[j]) % n for (i, j) in pairs}
    cnt = 0
    for (p1, e1), (p2, e2) in combinations(pe.items(), 2):
        if (e1 - e2) % n == s:      # antipodal products
            cnt += 1
    return cnt

ppc = Counter(pp_events(O, m) for O, m, h, v, k, p in recs)
print("antipodal product-product pairs per (O,mask) class ('E5' census):",
      dict(sorted(ppc.items())))
