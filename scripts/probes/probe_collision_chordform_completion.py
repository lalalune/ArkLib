#!/usr/bin/env python3
"""#357 converse increment 4c: complete the collision chart —
(a) the (2^6) three-quartet profile, scanned directly;
(b) the chord-form COMPLETION of every chord-side route: a collided structure with a
    derivable antipodal pair must derive the full chord form (difference-class equality
    + chord congruence, one of two orientations at that labeling) — the collided
    analogue of the chord branch. Report any structure where it does not.

Expected: zero incomplete chord routes, zero open (2^6) structures — then the
collision-branch Lean emission has complete targets.
"""
from itertools import product, combinations

EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),
    (1,1,1,0,0,0), (1,1,0,1,0,0),
    (1,0,0,0,1,1), (0,1,0,0,1,1),
    (0,0,1,1,1,0), (0,0,1,1,0,1),
    (1,0,1,1,0,0), (0,1,1,1,0,0),
    (1,1,0,0,1,0), (1,1,0,0,0,1),
]
SHIFT = [0,0,1,1,1,1,1,1,0,0,0,0]
def esv(i): return tuple(list(EXPVEC[i]) + [SHIFT[i]])
def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vadd(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(c,u): return tuple(c*x for x in u)
ZERO7 = tuple([0]*7)
def unit7(i): return tuple(1 if k==i else 0 for k in range(7))
EH = unit7(6)

def coin_diff(x, y): return vsub(esv(x), esv(y))
def pair_diff(x, v): return vsub(vsub(esv(v), esv(x)), EH)

KILLS = []
for i in range(6):
    for j in range(i+1,6):
        KILLS.append(vsub(unit7(i), unit7(j)))
for (i,j) in [(0,1),(0,2),(1,2)]:
    sv_i = vadd(unit7(2*i), unit7(2*i+1)); sv_j = vadd(unit7(2*j), unit7(2*j+1))
    KILLS.append(vsub(sv_i, sv_j))
ANTIPS = [vsub(vsub(unit7(2*i+1), unit7(2*i)), EH) for i in range(3)]

def solve(rows, target, maxc=2):
    k = len(rows)
    rng = range(-maxc, maxc+1)
    half = k//2
    first = {}
    for lam1 in product(rng, repeat=half):
        v = ZERO7
        for i,l in enumerate(lam1):
            if l: v = vadd(v, smul(l, rows[i]))
        first.setdefault(v, lam1)
    for lam2 in product(rng, repeat=k-half):
        v2 = ZERO7
        for i,l in enumerate(lam2):
            if l: v2 = vadd(v2, smul(l, rows[half+i]))
        need = vsub(target, v2)
        body = need[:6]
        for v1, lam1 in first.items():
            if v1[:6] != body: continue
            dh = need[6] - v1[6]
            if dh % 2 == 0:
                return (lam1 + lam2, dh//2)
    return None

def killed(rows, depth=0):
    for tv in KILLS:
        if solve(rows, tv) is not None or solve(rows, smul(-1, tv)) is not None:
            return True
    if depth < 1:
        for i in range(6):
            for j in range(i+1, 6):
                tv2 = smul(2, vsub(unit7(i), unit7(j)))
                if solve(rows, tv2) is None: continue
                extra = vsub(vsub(unit7(i), unit7(j)), EH)
                if killed(rows + [extra], depth+1):
                    return True
    return False

def antip_fired(rows):
    return [i for i in range(3) if solve(rows, ANTIPS[i]) is not None]

# chord forms per labeling i (the antipodal pair), two orientations.
# labeling 2 (pair index 1 in 0-based: A2,B2 antipodal): pairs 1,3 share class:
#   (A1-B1)-(A3-B3) = 0  &  2*A2 - A1 - B3 = 0   |  (A1-B1)+(A3-B3) = 0 & 2*A2 - A1 - A3 = 0
def chord_targets(lab):
    # lab in {0,1,2} = antipodal point index; other two points p<q
    others = [k for k in range(3) if k != lab]
    p, q = others
    Ap, Bp, Aq, Bq = unit7(2*p), unit7(2*p+1), unit7(2*q), unit7(2*q+1)
    K = unit7(2*lab)
    d1 = vsub(vsub(Ap, Bp), vsub(Aq, Bq))
    c1 = vsub(vsub(smul(2, K), Ap), Bq)
    d2 = vadd(vsub(Ap, Bp), vsub(Aq, Bq))
    c2 = vsub(vsub(smul(2, K), Ap), Aq)
    return [(d1, c1), (d2, c2)]

def chord_complete(rows, labs):
    for lab in labs:
        for (dv, cv) in chord_targets(lab):
            if solve(rows, dv) is not None and solve(rows, cv) is not None:
                return True
    return False

def parse_goal(g):
    NM = {'a1':0,'b1':1,'a2':2,'b2':3,'a3':4,'b3':5}
    lhs, rhs = g.split('=')
    v = ZERO7
    for t in lhs.strip().split('+'): v = vadd(v, unit7(NM[t.strip()]))
    for t in rhs.strip().split('+'):
        t = t.strip()
        if t == 'h': v = vsub(v, EH)
        else: v = vsub(v, unit7(NM[t]))
    return v
SYS = [
    ["b2+b3 = a1+b1+h", "a3+b3 = a1+b2+h", "a2+b2 = a1+b3+h"],
    ["b2+a3 = a1+b1+h", "a3+b3 = a1+b2+h", "a2+b2 = a1+a3+h"],
    ["b2+b3 = a1+b1+h", "a3+b3 = b1+b2+h", "a2+b2 = b1+b3+h"],
    ["b2+a3 = a1+b1+h", "a3+b3 = b1+b2+h", "a2+b2 = b1+a3+h"],
    ["a2+b3 = a1+b1+h", "a3+b3 = a1+a2+h", "a2+b2 = a1+b3+h"],
    ["a2+b3 = a1+b1+h", "a3+b3 = b1+a2+h", "a2+b2 = b1+b3+h"],
    ["a2+a3 = a1+b1+h", "a3+b3 = a1+a2+h", "a2+b2 = a1+a3+h"],
    ["a2+a3 = a1+b1+h", "a3+b3 = b1+a2+h", "a2+b2 = b1+a3+h"],
]
SYSV = [[parse_goal(g) for g in s] for s in SYS]
def second(rows):
    return any(all(solve(rows, tv) is not None for tv in tvs) for tvs in SYSV)

def quartet_rows(xy, zw):
    return [coin_diff(*xy), coin_diff(*zw), pair_diff(xy[0], zw[0])]

def pairings(elems):
    if not elems: yield []
    else:
        x = elems[0]
        for y in elems[1:]:
            rest = [e for e in elems[1:] if e != y]
            for p in pairings(rest):
                yield [(x,y)] + p

idx = list(range(12))
# pass (b): one-quartet chord-side completion
incomplete = []
n1 = 0; comp1 = 0
for xy in combinations(idx, 2):
    for zw in combinations([i for i in idx if i not in xy], 2):
        base = quartet_rows(xy, zw)
        rest = [i for i in idx if i not in xy and i not in zw]
        for P in pairings(rest):
            rows = base + [pair_diff(x, v) for (x,v) in P]
            if killed(rows): continue
            labs = antip_fired(rows)
            if labs:
                n1 += 1
                if chord_complete(rows, labs): comp1 += 1
                else:
                    # not directly chord-complete: check second-layer or flag
                    if not second(rows):
                        incomplete.append(('1Q', xy, zw, tuple(P), labs))
print(f"one-quartet chord-side: {n1}, chord-form complete: {comp1}, "
      f"flagged: {len(incomplete)}")

# pass (a)+(b): three-quartet (2^6) structures
n3 = 0; res3 = {'KILL':0,'CHORDC':0,'CHORDI':0,'SECOND':0,'OPEN':0}
seen = set()
for q1xy in combinations(idx, 2):
    r1 = [i for i in idx if i not in q1xy]
    for q1zw in combinations(r1, 2):
        r2 = [i for i in r1 if i not in q1zw]
        for q2xy in combinations(r2, 2):
            if q2xy[0] != r2[0]: break
            r3 = [i for i in r2 if i not in q2xy]
            for q2zw in combinations(r3, 2):
                r4 = [i for i in r3 if i not in q2zw]
                for q3zw_split in [((r4[0], r4[1]), (r4[2], r4[3])),
                                   ((r4[0], r4[2]), (r4[1], r4[3])),
                                   ((r4[0], r4[3]), (r4[1], r4[2]))]:
                    q3xy, q3zw = q3zw_split
                    n3 += 1
                    rows = (quartet_rows(q1xy, q1zw) + quartet_rows(q2xy, q2zw)
                            + quartet_rows(q3xy, q3zw))
                    if killed(rows): res3['KILL'] += 1; continue
                    labs = antip_fired(rows)
                    if labs:
                        if chord_complete(rows, labs): res3['CHORDC'] += 1
                        else: res3['CHORDI'] += 1
                        continue
                    if second(rows): res3['SECOND'] += 1
                    else: res3['OPEN'] += 1
print(f"three-quartet structures: {n3}; {res3}")
for o in incomplete[:15]: print("  FLAGGED:", o)
print("DONE")
