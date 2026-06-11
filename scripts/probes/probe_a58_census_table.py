from itertools import combinations
from collections import Counter

def balanced(A, n, h):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))

def e1fold(A, n):
    half = n//2
    v = [0]*half
    for i in A:
        if i < half: v[i] += 1
        else: v[i-half] -= 1
    return tuple(v)

n = 16; h = 8
# a=5 value set: check rotation-orbit structure: values should be {zeta^j * c}?
sols5 = [A for A in combinations(range(n), 5) if balanced(A, n, h)]
vals5 = {e1fold(A, n) for A in sols5}
# rotation: multiply by zeta = shift exponents by 1 (with sign wrap)
def rot(v):
    half = len(v)
    return tuple([-v[-1]] + list(v[:-1]))
orb_closed = all(rot(v) in vals5 for v in vals5)
print(f"a=5: census={len(vals5)}, rotation-closed={orb_closed}")
# is it ONE orbit? pick one, generate
v0 = next(iter(vals5)); orb = set(); v = v0
for _ in range(2*n):
    orb.add(v); v = rot(v)
print(f"a=5: single-orbit={orb == vals5} (orbit size {len(orb)})")

# a=8 vs a=4 value sets
sols4 = [A for A in combinations(range(n), 4) if balanced(A, n, h)]
sols8 = [A for A in combinations(range(n), 8) if balanced(A, n, h)]
v4 = {e1fold(A, n) for A in sols4}
v8 = {e1fold(A, n) for A in sols8}
print(f"a=8: census={len(v8)}, a=4 census={len(v4)}, SAME SET={v4 == v8}")
# a=9
sols9 = [A for A in combinations(range(n), 9) if balanced(A, n, h)]
v9 = {e1fold(A, n) for A in sols9}
v5 = vals5
print(f"a=9: balanced={len(sols9)}, census={len(v9)}, same-as-a5={v9 == v5}")
# a=12, a=13 (next even-pair rows)
sols12 = [A for A in combinations(range(n), 12) if balanced(A, n, h)]
v12 = {e1fold(A, n) for A in sols12}
print(f"a=12: balanced={len(sols12)}, census={len(v12)}, same-as-a4={v12 == v4}")
sols13 = [A for A in combinations(range(n), 13) if balanced(A, n, h)]
v13 = {e1fold(A, n) for A in sols13}
print(f"a=13: balanced={len(sols13)}, census={len(v13)}, same-as-a5={v13 == v5}")
# a=16 (full set)
sols16 = [A for A in combinations(range(n), 16) if balanced(A, n, h)]
print(f"a=16: balanced={len(sols16)}")
