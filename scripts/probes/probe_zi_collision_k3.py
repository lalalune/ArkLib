# Z[i]-collision analysis, k = 3 classes (profile permutations of (3,3,2)):
# coset-free 8-set in 3 coset classes at positions x1,x2,x3 (distinct mod N), contents
# B1,B2,B3 subsets of mu4 with sizes summing to 8, no size 4. Labels: D1,D2,D3 (exps 2*xi)
# and S12,S13,S23 (exps xi+xj), values in Z_{2N}; per-basis-residue (mod N) sums with
# i^(exp div N) twists must vanish in Z[i]. We enumerate ALL collision partitions of the
# 6 labels + epsilon bits, IGNORING realizability (superset): if nothing survives, the
# (3,3,2)-profile is impossible at EVERY scale.
from itertools import combinations, product

mu4 = [(1,0),(0,1),(-1,0),(0,-1)]  # 1, i, -1, -i as (re, im) in Z[i]
def gmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gadd(a,b): return (a[0]+b[0], a[1]+b[1])
def gsum(l):
    r = (0,0)
    for x in l: r = gadd(r,x)
    return r
def e1(B): return gsum(B)
def e2(B):
    r = (0,0)
    for p in combinations(B,2): r = gadd(r, gmul(*p))
    return r
I = (0,1)
def itw(eps, c): return c if eps == 0 else gmul(I, c)

subsets = {}
for sz in (1,2,3):
    subsets[sz] = [list(c) for c in combinations(mu4, sz)]

def partitions(labels):
    if not labels: yield []
    else:
        first, rest = labels[0], labels[1:]
        for p in partitions(rest):
            for k in range(len(p)):
                yield p[:k] + [p[k]+[first]] + p[k+1:]
            yield p + [[first]]

# label order: D1 D2 D3 S12 S13 S23; relations among exponents:
# D1+D2 = 2*S12 etc (mod 2N) — we IGNORE these (superset check).
labels = list(range(6))
LD = [0,1,2]; LS = {(0,1):3, (0,2):4, (1,2):5}
count_surv = 0
for sizes in [(3,3,2),(3,2,3),(2,3,3)]:
    for B1 in subsets[sizes[0]]:
        for B2 in subsets[sizes[1]]:
            for B3 in subsets[sizes[2]]:
                Bs = [B1,B2,B3]
                coeff = {0: e2(B1), 1: e2(B2), 2: e2(B3),
                         3: gmul(e1(B1),e1(B2)), 4: gmul(e1(B1),e1(B3)),
                         5: gmul(e1(B2),e1(B3))}
                for part in partitions(labels):
                    # quick check: any class whose coeffs can't cancel?
                    ok_any_eps = False
                    for eps in product((0,1), repeat=6):
                        good = True
                        for cls in part:
                            s = gsum([itw(eps[t], coeff[t]) for t in cls])
                            if s != (0,0):
                                good = False; break
                        if good:
                            ok_any_eps = True; break
                    if ok_any_eps:
                        count_surv += 1
print("surviving (sizes,B,partition) combos (pre-realizability):", count_surv)
