#!/usr/bin/env python3
"""#357 converse increment 3: the NO-antipodal branch case tree, with kill certificates.

Generic branch with NO antipodal pair (the second-layer stratum). All three antipodal
conditions are now kills; the canonical matching has no within-block and no cross-sign
pairs that survive locally — this probe enumerates the full tree the way Lean will walk
it (partner of 0, then partner of the smallest unmatched index, ...), printing per-leaf
kill certificates and the surviving systems (expected: the 8 second-layer patterns plus
their orientation images).

Walk order and node structure are emitted so the Lean transcription can mirror them.
"""
from itertools import combinations

EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),    # 0,1   e2*m3  [+]
    (1,1,1,0,0,0), (1,1,0,1,0,0),    # 2,3   e2*m1  [-]
    (1,0,0,0,1,1), (0,1,0,0,1,1),    # 4,5   e1*m3  [-]
    (0,0,1,1,1,0), (0,0,1,1,0,1),    # 6,7   e3*m2  [-]
    (1,0,1,1,0,0), (0,1,1,1,0,0),    # 8,9   e1*m2  [+]
    (1,1,0,0,1,0), (1,1,0,0,0,1),    # 10,11 e3*m1  [+]
]
SIGN = [1,1,-1,-1,-1,-1,-1,-1,1,1,1,1]
NAMES = ['a1','b1','a2','b2','a3','b3']

def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vneg(u): return tuple(-x for x in u)
def unit(i): return tuple(1 if k==i else 0 for k in range(6))

def pair_congruence(x, y):
    vec = vsub(EXPVEC[x], EXPVEC[y])
    flag = 1 if SIGN[x]==SIGN[y] else 0
    return vec, flag

TARGETS = []
for i in range(6):
    for j in range(i+1,6):
        TARGETS.append((vsub(unit(i),unit(j)), 0, f'D6:{NAMES[i]}={NAMES[j]}'))
SVEC = [ (1,1,0,0,0,0), (0,0,1,1,0,0), (0,0,0,0,1,1) ]
for i in range(3):
    for j in range(i+1,3):
        TARGETS.append((vsub(SVEC[i],SVEC[j]), 0, f'GEN:s{i+1}=s{j+1}'))
for i in range(3):
    TARGETS.append((vsub(unit(2*i),unit(2*i+1)), 1, f'ANTIP{i+1}'))
MULT = []
for x in range(12):
    for y in range(x+1,12):
        MULT.append((vsub(EXPVEC[x],EXPVEC[y]), 0 if SIGN[x]==SIGN[y] else 1,
                     f'MULT:{x},{y}'))

def lattice_solve(rows, flags, tv, tf, maxc=2):
    from itertools import product
    k = len(rows)
    half = k//2
    first = {}
    rng = range(-maxc, maxc+1)
    for lam1 in product(rng, repeat=half):
        v = tuple(sum(l*rows[i][t] for i,l in enumerate(lam1)) for t in range(6))
        f = sum(l*flags[i] for i,l in enumerate(lam1)) % 2
        first.setdefault((v,f), lam1)
    for lam2 in product(rng, repeat=k-half):
        v2 = tuple(sum(l*rows[half+i][t] for i,l in enumerate(lam2)) for t in range(6))
        f2 = sum(l*flags[half+i] for i,l in enumerate(lam2)) % 2
        need = (vsub(tv, v2), (tf - f2) % 2)
        if need in first:
            return first[need] + lam2
    return None

def kill_search(rows, flags, mset, depth=0):
    for tv, tf, kind in TARGETS:
        for sgn in (1,-1):
            lam = lattice_solve(rows, flags, tuple(sgn*t for t in tv), tf)
            if lam is not None:
                return (kind, sgn, lam)
    for tv, tf, kind in MULT:
        x,y = map(int, kind.split(':')[1].split(','))
        if frozenset((x,y)) in mset: continue
        for sgn in (1,-1):
            lam = lattice_solve(rows, flags, tuple(sgn*t for t in tv), tf)
            if lam is not None:
                return (kind, sgn, lam)
    if depth < 1:
        for i in range(6):
            for j in range(i+1,6):
                tv2 = tuple(2*t for t in vsub(unit(i),unit(j)))
                lam = lattice_solve(rows, flags, tv2, 0)
                if lam is None: continue
                sub = kill_search(rows + [vsub(unit(i),unit(j))], flags + [1],
                                  mset, depth+1)
                if sub is not None:
                    return (f'BRANCH({NAMES[i]}-{NAMES[j]})', lam, sub)
    return None

def fmt(vec, flag):
    terms=[]
    for c,nm in zip(vec,NAMES):
        if c==0: continue
        terms.append(('+' if c>0 else '-') + (nm if abs(c)==1 else f'{abs(c)}{nm}'))
    return ''.join(terms).lstrip('+') + (' = h' if flag else ' = 0')

def pairings(elems):
    if not elems: yield []
    else:
        x = elems[0]
        for y in elems[1:]:
            rest = [e for e in elems[1:] if e != y]
            for p in pairings(rest):
                yield [(x,y)] + p

count = 0; killed = 0; surv = []
killdepth = {}
for P in pairings(list(range(12))):
    count += 1
    rows = []; flags = []
    for (x,y) in P:
        v,f = pair_congruence(x,y)
        rows.append(v); flags.append(f)
    mset = {frozenset(p) for p in P}
    # find earliest killing prefix (for tree-shaping): try prefixes of length 1..6
    cert = None; dep = 6
    for k in range(1, 7):
        cert = kill_search(rows[:k], flags[:k], {frozenset(p) for p in P[:k]})
        if cert is not None:
            dep = k; break
    if cert is not None:
        killed += 1
        killdepth[dep] = killdepth.get(dep, 0) + 1
        if dep >= 3:
            print(f"LEAF {tuple(P)}: KILL@depth{dep} {cert[0]}  cert={cert[1:]}")
    else:
        surv.append(P)
print(f"\ntotal pairings: {count}, killed: {killed} (by prefix depth {killdepth}), "
      f"survivors: {len(surv)}")
for P in surv:
    print(f"\nSURVIVOR {tuple(P)}:")
    sys_ = set()
    for (x,y) in P:
        v,f = pair_congruence(x,y)
        sys_.add(min((v,f),(vneg(v),f)))
    for v,f in sorted(sys_): print("   ", fmt(v,f))
print("DONE")
