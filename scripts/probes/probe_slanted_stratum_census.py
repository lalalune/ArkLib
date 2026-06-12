#!/usr/bin/env python3
"""Item 2 core: the char-0 SLANTED stratum census. Pairs {i,j} -> point (s,p) =
(z^i + z^j, z^{i+j}) in Z[zeta_n]. Count collinear triples that are neither vertical
(equal s) nor horizontal (equal p), exactly via folding. Compare with the chord-law
supply (2k ≡ i+j+d) and seed families."""
from itertools import combinations

def make_ops(m):
    n = 1 << m; N = n >> 1
    def unit(t):  # folded vector of zeta^t
        t %= n
        v = [0]*N
        if t < N: v[t] = 1
        else: v[t-N] = -1
        return v
    def add(a,b): return [x+y for x,y in zip(a,b)]
    def sub(a,b): return [x-y for x,y in zip(a,b)]
    def mul(a,b):
        # convolution with fold X^N = -1
        r = [0]*N
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b):
                    if y:
                        t = i+j
                        if t < N: r[t] += x*y
                        else: r[t-N] -= x*y
        return r
    return n, N, unit, add, sub, mul

def census(m, verbose=False):
    n, N, unit, add, sub, mul = make_ops(m)
    pairs = list(combinations(range(n), 2))
    pts = []
    for (i,j) in pairs:
        s = add(unit(i), unit(j))
        p = unit(i+j)
        pts.append(((i,j), s, p))
    cnt_slant = 0
    chord_explained = 0
    examples = []
    for (P1, P2, P3) in combinations(pts, 3):
        (pr1,s1,p1),(pr2,s2,p2),(pr3,s3,p3) = P1,P2,P3
        # det [[1,s1,p1],[1,s2,p2],[1,s3,p3]] = (s2-s1)(p3-p1)-(s3-s1)(p2-p1)
        d = sub(mul(sub(s2,s1), sub(p3,p1)), mul(sub(s3,s1), sub(p2,p1)))
        if any(d): continue
        # vertical: all s equal; horizontal: all p equal
        if not any(sub(s2,s1)) and not any(sub(s3,s1)): continue
        if not any(sub(p2,p1)) and not any(sub(p3,p1)): continue
        cnt_slant += 1
        # chord-law test: exists labeling with diffs (d,d) and antipodal pair + congruence
        diffs = [ (pr[1]-pr[0]) % n for pr in (pr1,pr2,pr3) ]
        anti = [ (pr[1]-pr[0]) % n == n//2 for pr in (pr1,pr2,pr3) ]
        is_chord = False
        for t in range(3):
            others = [x for x in range(3) if x != t]
            prs = [pr1,pr2,pr3]
            if anti[t] and diffs[others[0]] == diffs[others[1]]:
                dd = diffs[others[0]]
                i_, j_ = prs[others[0]][0], prs[others[1]][0]
                k_ = prs[t][0]
                if (2*k_ - (i_ + j_ + dd)) % n == 0:
                    is_chord = True
        if is_chord: chord_explained += 1
        elif len(examples) < 6: examples.append((pr1,pr2,pr3))
    return cnt_slant, chord_explained, examples

for m in (3, 4):
    c, ch, ex = census(m)
    print(f"n={1<<m}: slanted collinear triples = {c}, chord-law-explained = {ch}, UNEXPLAINED = {c-ch}")
    for e in ex: print(f"   unexplained: {e}")

print("\nDISJOINT-PAIR (6 distinct indices) slanted census:", flush=True)
def census2(m):
    n, N, unit, add, sub, mul = make_ops(m)
    pairs = list(combinations(range(n), 2))
    pts = []
    for (i,j) in pairs:
        pts.append(((i,j), add(unit(i), unit(j)), unit(i+j)))
    cnt = 0; chord = 0; ex = []
    for (P1,P2,P3) in combinations(pts, 3):
        (pr1,s1,p1),(pr2,s2,p2),(pr3,s3,p3) = P1,P2,P3
        idx = set(pr1)|set(pr2)|set(pr3)
        if len(idx) != 6: continue
        d = sub(mul(sub(s2,s1), sub(p3,p1)), mul(sub(s3,s1), sub(p2,p1)))
        if any(d): continue
        if not any(sub(s2,s1)) and not any(sub(s3,s1)): continue
        if not any(sub(p2,p1)) and not any(sub(p3,p1)): continue
        cnt += 1
        diffs = [ (pr[1]-pr[0]) % n for pr in (pr1,pr2,pr3) ]
        anti = [ dd == n//2 for dd in diffs ]
        is_chord = False
        prs = [pr1,pr2,pr3]
        for t in range(3):
            o = [x for x in range(3) if x != t]
            if anti[t] and diffs[o[0]] == diffs[o[1]]:
                dd = diffs[o[0]]
                if (2*prs[t][0] - (prs[o[0]][0] + prs[o[1]][0] + dd)) % n == 0:
                    is_chord = True
        if is_chord: chord += 1
        elif len(ex) < 8: ex.append((pr1,pr2,pr3))
    return cnt, chord, ex

for m in (3, 4):
    c, ch, ex = census2(m)
    print(f"n={1<<m}: disjoint slanted triples = {c}, chord-explained = {ch}, UNEXPLAINED = {c-ch}")
    for e in ex: print(f"   unexplained: {e}")

print("\nCOMPLETENESS TEST: chords + shape-I/II orbits vs the census", flush=True)
def canon_triple(prs, n):
    return tuple(sorted(tuple(sorted((x % n) for x in pr)) for pr in prs))

def all_slanted(m):
    n, N, unit, add, sub, mul = make_ops(m)
    pts = [((i,j), add(unit(i),unit(j)), unit(i+j)) for (i,j) in combinations(range(n),2)]
    out = set()
    for (P1,P2,P3) in combinations(pts,3):
        (pr1,s1,p1),(pr2,s2,p2),(pr3,s3,p3) = P1,P2,P3
        if len(set(pr1)|set(pr2)|set(pr3)) != 6: continue
        d = sub(mul(sub(s2,s1),sub(p3,p1)), mul(sub(s3,s1),sub(p2,p1)))
        if any(d): continue
        if not any(sub(s2,s1)) and not any(sub(s3,s1)): continue
        if not any(sub(p2,p1)) and not any(sub(p3,p1)): continue
        out.add(canon_triple((pr1,pr2,pr3), n))
    return out

def families(m):
    n = 1 << m
    fams = set()
    def add_orbit(prs):
        base = [tuple(pr) for pr in prs]
        idx = set()
        for pr in base: idx |= set(pr)
        if len(idx) != 6: return
        for u in range(1, n, 2):
            for c in range(n):
                img = [((u*x+c) % n, (u*y+c) % n) for (x,y) in base]
                if len(set.union(*[set(pr) for pr in img])) != 6: continue
                fams.add(canon_triple(img, n))
    # chord family (d,d,anti) with congruence
    for d in range(1, n):
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if (2*k - (i+j+d)) % n: continue
                    add_orbit([(i,(i+d)%n), (j,(j+d)%n), (k,(k+n//2)%n)])
    # shapes
    for t in range(n//2):
        add_orbit([(0,1), ((t+1)%n, (n-(2*t+1))%n), ((2*t+1)%n, (n//2-t)%n)])
        if t+1 < n//2:
            add_orbit([(0,1), ((t+2)%n, (n-(2*t+2))%n), ((2*t+4)%n, (n//2-(t+1))%n)])
    return fams

for m in (3, 4):
    n = 1 << m
    cen = all_slanted(m)
    fam = families(m)
    print(f"n={n}: census = {len(cen)}, families-generated = {len(fam)}, "
          f"explained = {len(cen & fam)}, UNEXPLAINED = {len(cen - fam)}, spurious = {len(fam - cen)}")
    for e in list(cen - fam)[:5]: print(f"   unexplained: {e}")
