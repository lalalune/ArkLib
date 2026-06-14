# Enumerate the F2-admissible collision architectures for coset-free profiles at k=4:
# the definitive finite case list for the ContainsCosetHyp formalization campaign.
from itertools import combinations

def partitions(labels):
    if not labels: yield []
    else:
        first, rest = labels[0], labels[1:]
        for p in partitions(rest):
            for i in range(len(p)):
                yield p[:i] + [p[i]+[first]] + p[i+1:]
            yield p + [[first]]

def compatible(a, b):
    # can labels a, b share a residue class? D_i = ('D', i); S_ij = ('S', i, j)
    if a[0]=='D' and b[0]=='D': return True               # x_j = x_i + N/2
    if a[0]=='D' and b[0]=='S': return a[1] not in b[1:]  # 2x_i = x_j + x_l
    if a[0]=='S' and b[0]=='D': return b[1] not in a[1:]
    return not (set(a[1:]) & set(b[1:]))                  # S~S need disjoint

def admissible_count(k, sizes, antipodal):
    # antipodal: set of indices with antipodal size-2 content (sigma = 0)
    units_sigma = [i for i in range(k) if sizes[i] in (1,3)]
    nu1_sigma   = [i for i in range(k) if sizes[i]==2 and i not in antipodal]
    Dlabels = [('D', i) for i in range(k) if sizes[i] in (2,3)]   # e2 unit
    Slabels = []
    for i, j in combinations(range(k), 2):
        if i in antipodal or j in antipodal: continue              # sigma = 0
        Slabels.append(('S', i, j))
    def is_unit(lbl):
        if lbl[0]=='D': return True
        i, j = lbl[1], lbl[2]
        return (i in units_sigma) and (j in units_sigma)           # else nu>=1
    labels = Dlabels + Slabels
    cnt = 0
    for part in partitions(labels):
        ok = True
        for cls in part:
            if len(cls) == 1: ok = False; break
            if any(not compatible(a, b) for a, b in combinations(cls, 2)):
                ok = False; break
            if sum(1 for l in cls if is_unit(l)) % 2 != 0:
                ok = False; break
        if ok: cnt += 1
    return cnt

total = 0
print("k=4 profiles (sizes, antipodal-2 subsets) -> admissible architectures:")
for sizes in [(3,3,1,1),(3,2,2,1),(2,2,2,2)]:
    twos = [i for i,s in enumerate(sizes) if s==2]
    for r in range(len(twos)+1):
        for anti in combinations(twos, r):
            c = admissible_count(4, sizes, set(anti))
            if c: print(f"  sizes={sizes} antipodal={anti}: {c}")
            total += c
print("TOTAL k=4 admissible architectures:", total)
