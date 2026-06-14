# Restricted-growth DFS with pruning for k = 6..8 admissible architectures.
from itertools import combinations
import sys, time

def compatible(a, b):
    if a[0]=='D' and b[0]=='D': return True
    if a[0]=='D' and b[0]=='S': return a[1] not in b[1:]
    if a[0]=='S' and b[0]=='D': return b[1] not in a[1:]
    return not (set(a[1:]) & set(b[1:]))

def count_arch(k, sizes, antipodal, deadline):
    units_sigma = [i for i in range(k) if sizes[i] in (1,3)]
    Dlabels = [('D', i) for i in range(k) if sizes[i] in (2,3)]
    Slabels = [('S', i, j) for i, j in combinations(range(k), 2)
               if i not in antipodal and j not in antipodal]
    def is_unit(lbl):
        if lbl[0]=='D': return True
        return (lbl[1] in units_sigma) and (lbl[2] in units_sigma)
    labels = Dlabels + Slabels
    L = len(labels)
    cnt = 0
    # classes: list of (members, unit_parity, size)
    def dfs(idx, classes):
        nonlocal cnt
        if time.time() > deadline: raise TimeoutError
        rem = L - idx
        # deficiency prune: each class needs size>=2 and even units
        need = 0
        for mem, par, sz in classes:
            need += max(2 - sz, 1 if par else 0) if (sz < 2 or par) else 0
        if need > rem: return
        if idx == L:
            if need == 0: cnt += 1
            return
        lbl = labels[idx]; u = is_unit(lbl)
        for ci in range(len(classes)):
            mem, par, sz = classes[ci]
            if all(compatible(lbl, x) for x in mem):
                classes[ci] = (mem + [lbl], par ^ u, sz + 1)
                dfs(idx + 1, classes)
                classes[ci] = (mem, par, sz)
        classes.append(([lbl], u, 1))
        dfs(idx + 1, classes)
        classes.pop()
    try:
        dfs(0, [])
        return cnt
    except TimeoutError:
        return None

def profiles(total, maxpart, k):
    if k == 0:
        if total == 0: yield []
        return
    for p in range(min(maxpart,total), 0, -1):
        for rest in profiles(total-p, p, k-1):
            yield [p]+rest

for k in (6, 7, 8):
    ktotal = 0; incomplete = False
    for prof in profiles(8, 3, k):
        sizes = tuple(prof)
        twos = [i for i,s in enumerate(sizes) if s==2]
        for r in range(len(twos)+1):
            for anti in combinations(twos, r):
                c = count_arch(k, sizes, set(anti), time.time() + 120)
                if c is None:
                    print(f"  k={k} sizes={sizes} anti={anti}: TIMEOUT", flush=True)
                    incomplete = True
                elif c:
                    print(f"  k={k} sizes={sizes} anti={anti}: {c}", flush=True)
                    ktotal += c
    print(f"k={k} TOTAL: {ktotal}{' (INCOMPLETE)' if incomplete else ''}", flush=True)
