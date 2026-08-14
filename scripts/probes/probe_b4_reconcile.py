import itertools, cmath, math
from collections import defaultdict

def roots(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def esymm(vals, h):
    es = [0j]*(h+1); es[0] = 1+0j
    for v in vals:
        for k in range(h, 0, -1):
            es[k] += es[k-1]*v
    return es[1:]

def multiset_eq(A, B, tol=1e-6):
    B = list(B)
    for a in A:
        ok = False
        for i, b in enumerate(B):
            if abs(a-b) < tol:
                B.pop(i); ok = True; break
        if not ok:
            return False
    return True

# Reconcile: among (e1,e4) classes with multiple e2, what is e1 there? And do they collide
# as MULTISETS? Report classes where the multiset genuinely differs, with their e1 magnitude.
for n in [4, 8, 16]:
    R = roots(n)
    by = defaultdict(list)
    for t in itertools.combinations_with_replacement(range(n), 4):
        e1, e2, e3, e4 = esymm([R[i] for i in t], 4)
        key = (round(e1.real,6), round(e1.imag,6), round(e4.real,6), round(e4.imag,6))
        by[key].append((t, abs(e1)))
    bad = 0; bad_with_nonzero_e1 = 0; total_pairs = 0
    for key, ts in by.items():
        for (a, ea), (b, eb) in itertools.combinations(ts, 2):
            total_pairs += 1
            if not multiset_eq([R[i] for i in a], [R[i] for i in b]):
                bad += 1
                if ea > 1e-6:
                    bad_with_nonzero_e1 += 1
    print(f"n={n:3d}: (e1,e4)-fixed multiset collisions total={bad}/{total_pairs} | "
          f"with e1 != 0: {bad_with_nonzero_e1}")
