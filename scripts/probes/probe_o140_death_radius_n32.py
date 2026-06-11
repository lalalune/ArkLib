# Death-radius scaling at n=32, rate 1/4 (k=8), p in {97, 193}:
# qualifying counts for a=10 (c=2: e2=0) and a=11 (c=3: e2=e3=0).
# n=16 verdict was: alive at c=2, dead at c=3 (p>=97). Constant-c death => family reach
# = capacity - O(1/n); growing-c => interior reach.
from itertools import combinations
import sys
def subgroup(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p-1):
            x = x*g % p; elems.add(x)
        if len(elems) == p-1:
            gen = pow(g, (p-1)//n, p)
            H = sorted(set(pow(gen, i, p) for i in range(n)))
            assert len(H) == n
            return H
for p in (97, 193):
    H = subgroup(p, 32)
    sq = {x: x*x % p for x in H}
    cb = {x: x*x*x % p for x in H}
    inv2 = pow(2, p-2, p)
    # a=10, constraint e2=0  <=>  p1^2 = p2
    cnt2 = 0
    found2 = None
    for A in combinations(H, 10):
        s1 = sum(A) % p
        s2 = sum(sq[x] for x in A) % p
        if (s1*s1 - s2) % p == 0:
            cnt2 += 1
            if found2 is None: found2 = A
    print(f"p={p} a=10 (c=2): qualifying = {cnt2}", flush=True)
    # a=11, constraints e2=e3=0 <=> p2=p1^2 and (via Newton w/ e1=p1, e2=0):
    # e3 = (p1^3 - 3 p1 p2 + 2 p3)/6 = 0  <=> 2 p3 = 3 p1 p2 - p1^3 ; with p2 = p1^2:
    # 2 p3 = 2 p1^3  <=> p3 = p1^3
    cnt3 = 0
    found3 = None
    for A in combinations(H, 11):
        s1 = sum(A) % p
        s2 = sum(sq[x] for x in A) % p
        if (s1*s1 - s2) % p: continue
        s3 = sum(cb[x] for x in A) % p
        if (s3 - pow(s1, 3, p)) % p == 0:
            cnt3 += 1
            if found3 is None: found3 = A
    print(f"p={p} a=11 (c=3): qualifying = {cnt3}", flush=True)
print("done")
