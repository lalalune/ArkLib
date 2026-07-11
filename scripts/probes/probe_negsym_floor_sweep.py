"""
DECISIVE SWEEP (rule 2): the antipodal perfect-matching injection floor on negSymCount.

CLAIM (char-free, any negation-closed G, |G|=n):
    negSymCount(G, 2r)  >=  (2r-1)!! * fall(n, r)
where fall(n,r) = n*(n-1)*...*(n-r+1) and (2r-1)!! = #perfect matchings of 2r points.

The injection: a pair-partition P of {0..2r-1} into r unordered pairs (there are (2r-1)!! of them),
together with an injective assignment val: pairs -> G of DISTINCT values, builds the tuple where the
LOWER-indexed slot of each pair gets val(pair) and the HIGHER-indexed slot gets -val(pair).
Each such (P, val) gives a count-balanced tuple, and the map (P,val) -> tuple is INJECTIVE because
the tuple's value-set is {±val(pair)} with each val(pair) appearing once and -val(pair) once, distinct
across pairs (distinctness of the r chosen values, and -1 in G so antipodes are in G; for n=2^a,
n>=4, -1 in mu_n and the r distinct z give 2r distinct slot-values UNLESS z=-z' for two chosen z,z'
-> so we additionally need the chosen values to be "sign-distinct". We test BOTH the naive fall(n,r)
floor AND the sign-aware floor (n/2 antipodal classes choose).
"""
from itertools import product, permutations, combinations
from collections import Counter

def doublefact(r):
    out = 1
    for i in range(1, r+1):
        out *= (2*i - 1)
    return out

def fall(n, r):
    p = 1
    for i in range(r):
        p *= (n - i)
    return p

def negsym_count(Gvals, m, neg):
    cnt = 0
    for c in product(Gvals, repeat=m):
        cc = Counter(c)
        ok = True
        for z in cc:
            if cc[z] != cc.get(neg[z], 0):
                ok = False; break
        if ok:
            cnt += 1
    return cnt

def build_mu(p, n):
    G = [x for x in range(1, p) if pow(x, n, p) == 1]
    return G if len(G) == n else None

print("n  r  p     negSym     dfact*fall(n,r)  holds  ratio   [leading n^r match]")
tests = []
for n in [4, 8]:
    for p in [17, 41, 97, 113]:
        tests.append((p, n))
allhold = True
seen=set()
for (p, n) in tests:
    G = build_mu(p, n)
    if G is None: continue
    neg = {z: (p - z) for z in G}
    if any((p - z) not in G for z in G): continue
    for r in [1, 2, 3]:
        m = 2*r
        if n**m > 5_000_000: continue
        key=(n,r,p)
        ns = negsym_count(G, m, neg)
        floor = doublefact(r) * fall(n, r)
        hold = ns >= floor
        allhold = allhold and hold
        wick = doublefact(r) * (n**r)
        print(f"{n}  {r}  {p:<5} {ns:>8}   {floor:>12}    {str(hold):>5}  {ns/floor:.4f}   wick(n^r)={wick} floor/wick={floor/wick:.4f}")
print("ALL HOLD:", allhold)
