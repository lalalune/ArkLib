import itertools, cmath, math
from collections import defaultdict

def roots(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def esymm(vals, h):
    es = [0j]*(h+1); es[0] = 1+0j
    for v in vals:
        for k in range(h, 0, -1):
            es[k] += es[k-1]*v
    return es[1:]   # e_1..e_h

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

def rkey(z):
    return (round(z.real, 6), round(z.imag, 6))

def test(n, h, idxs, skip_zero_sum=True):
    """idxs = which elementary symmetric functions (1-based) we FIX. Check if fixing them forces
    the multiset.

    NOTE (honesty): by default we RESTRICT to e_1 != 0 (skip_zero_sum=True), because the 4-element
    rung genuinely FAILS for zero-sum quadruples even with (e_1, e_4) fixed -- see probe_b4_reconcile.py
    (all (e_1,e_4)-collisions have e_1 = 0). The Lean wrapper carries an e_1 != 0 hypothesis, so this
    restriction matches the claim. Pass skip_zero_sum=False to see the unrestricted (zero-sum-included)
    counts."""
    R = roots(n)
    by = defaultdict(list)
    for t in itertools.combinations_with_replacement(range(n), h):
        es = esymm([R[i] for i in t], h)
        if skip_zero_sum and abs(es[0]) < 1e-7:
            continue
        key = tuple(rkey(es[i-1]) for i in idxs)
        by[key].append(t)
    coll = 0; pairs = 0
    for ts in by.values():
        for a, b in itertools.combinations(ts, 2):
            pairs += 1
            if not multiset_eq([R[i] for i in a], [R[i] for i in b]):
                coll += 1
    return coll, pairs

# conjugation relations for 4 roots of unity (conj x = 1/x):
#   conj(e1) = e3/e4 ;  conj(e2) = e2/e4 ;  conj(e3) = e1/e4 ; e4 = product (|e4|=1)
# so fixing (e1, e4) -> e3 free; e2 must be supplied (self-conjugate up to e4).
# Test which subsets force the 4-multiset.
print("=== RESTRICTED to e_1 != 0 (matches the Lean wrapper's hypothesis) ===")
for n in [4, 8, 16]:
    h = 4
    for idxs in [(1,), (1,4), (1,2,4), (1,2,3,4), (1,3,4), (1,2)]:
        coll, pairs = test(n, h, idxs, skip_zero_sum=True)
        tag = "e_" + ",".join(str(i) for i in idxs)
        print(f"n={n:3d} h=4 fix[{tag:10s}] (e_1!=0): collisions={coll}/{pairs}")
    print()

print("=== UNRESTRICTED (zero-sum quadruples INCLUDED -- shows the e_1=0 failure) ===")
for n in [4, 8, 16]:
    h = 4
    for idxs in [(1,), (1,4), (1,2,4)]:
        coll, pairs = test(n, h, idxs, skip_zero_sum=False)
        tag = "e_" + ",".join(str(i) for i in idxs)
        print(f"n={n:3d} h=4 fix[{tag:10s}] (all)   : collisions={coll}/{pairs}")
    print()
