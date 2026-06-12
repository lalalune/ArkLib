# Extend the admissible-architecture enumeration to k = 5..8 (all coset-free 8-set
# profiles). Same filters: pairwise compatibility, no nonzero singleton classes,
# F2 even-unit law per class.
from itertools import combinations
import sys
sys.setrecursionlimit(10000)

def partitions(labels):
    if not labels: yield []
    else:
        first, rest = labels[0], labels[1:]
        for p in partitions(rest):
            for i in range(len(p)):
                yield p[:i] + [p[i]+[first]] + p[i+1:]
            yield p + [[first]]

def compatible(a, b):
    if a[0]=='D' and b[0]=='D': return True
    if a[0]=='D' and b[0]=='S': return a[1] not in b[1:]
    if a[0]=='S' and b[0]=='D': return b[1] not in a[1:]
    return not (set(a[1:]) & set(b[1:]))

def admissible_count(k, sizes, antipodal):
    units_sigma = [i for i in range(k) if sizes[i] in (1,3)]
    Dlabels = [('D', i) for i in range(k) if sizes[i] in (2,3)]
    Slabels = [('S', i, j) for i, j in combinations(range(k), 2)
               if i not in antipodal and j not in antipodal]
    def is_unit(lbl):
        if lbl[0]=='D': return True
        return (lbl[1] in units_sigma) and (lbl[2] in units_sigma)
    labels = Dlabels + Slabels
    cnt = 0
    for part in partitions(labels):
        ok = True
        for cls in part:
            if len(cls) == 1: ok = False; break
            if any(not compatible(a,b) for a,b in combinations(cls,2)): ok=False; break
            if sum(1 for l in cls if is_unit(l)) % 2 != 0: ok=False; break
        if ok: cnt += 1
    return cnt

def profiles(total, maxpart, k):
    if k == 0:
        if total == 0: yield []
        return
    for p in range(min(maxpart,total), 0, -1):
        for rest in profiles(total-p, p, k-1):
            yield [p]+rest

grand = 0
for k in range(5, 9):
    ktotal = 0
    for prof in profiles(8, 3, k):
        # distinct orderings matter for the count but types are up to symmetry;
        # count one ordering per multiset (canonical sorted) and note multiplicity
        sizes = tuple(prof)
        twos = [i for i,s in enumerate(sizes) if s==2]
        for r in range(len(twos)+1):
            for anti in combinations(twos, r):
                c = admissible_count(k, sizes, set(anti))
                if c: print(f"  k={k} sizes={sizes} antipodal={anti}: {c}", flush=True)
                ktotal += c
    print(f"k={k} TOTAL (canonical size-order): {ktotal}", flush=True)
    grand += ktotal
print("GRAND TOTAL k=5..8:", grand)
