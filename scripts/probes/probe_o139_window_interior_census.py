# O139: first exact constrained-census data INSIDE the prize window.
# Rate 1/4 (n=16, k=4), window = (Johnson 0.5, capacity 0.75).
# census(a) = #{-e1(A) : A in C(mu_16, a), e2(A)=...=e_{a-4}(A)=0}, delta = 1 - a/16.
# Verdicts (exact):
#  a=5 (delta=.6875): no constraints (a=k+1) -> all C(16,5)=4368 subsets qualify; census
#     SATURATES the field (= p) at p in {17,97,113,193}: eps_ca = 1 above Johnson at small
#     fields for an explicit stack. At huge p census <= 4368: the t=1 sliver object.
#  a=6 (delta=.625): e2=0 -> field-DEPENDENT: (p,#qual,census) = (17,480,17), (97,80,32),
#     (113,48,48), (193,16,16) -- non-monotone in p, ~n-scale at large p.
#  a=7 (delta=.5625): e2=e3=0 -> EMPTY at p >= 97 (32 qualifying at p=17 only):
#     the adjacent-pair family DIES mid-window at large fields; death radius in
#     (0.5625, 0.625] at (16,4).
from itertools import combinations
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
def esymms(A, m, p):
    pws = [sum(pow(a, j, p) for a in A) % p for j in range(1, m+1)]
    e = [1]
    for j in range(1, m+1):
        s = 0
        for i in range(1, j+1):
            s += (-1)**(i-1) * e[j-i] * pws[i-1]
        e.append(s * pow(j, p-2, p) % p)
    return e[1:]
n, k = 16, 4
expected = {17: [(5,4368,17),(6,480,17),(7,32,16)],
            97: [(5,4368,97),(6,80,32),(7,0,0)],
            113: [(5,4368,113),(6,48,48),(7,0,0)],
            193: [(5,4368,193),(6,16,16),(7,0,0)]}
for p in (17, 97, 113, 193):
    H = subgroup(p, n)
    row = []
    for a in (5, 6, 7):
        ncon = a - k
        cnt, lams = 0, set()
        for A in combinations(H, a):
            e = esymms(A, ncon, p)
            if all(v == 0 for v in e[1:ncon]):
                cnt += 1; lams.add((-e[0]) % p)
        row.append((a, cnt, len(lams)))
    assert row == expected[p], (p, row)
    print(f"p={p}: (a, #qualifying, census) = {row}  [OK]")
print("window-interior census verdicts reproduced")
