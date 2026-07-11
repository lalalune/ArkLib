# O152 red-team cycle 3: the two-family profile law at (11,5,2) -- PRIME n=5 domain
# (mu_5 in F_11), no fiber/tower structure. Exact: profile {3:10, 4:2, 5:1} =
# max(staircase = n-a+1, census(a)) at every rung. census(5)=1 is the unique
# Lam-Leung prime-5 vanishing (the full group); census(4)=0 (no 4-subset vanishing
# possible at prime order); census(3)=10 (unconstrained sums, all distinct).
src = open("scripts/probes/probe_exact_epsmca_ladder.py").read().split("if __name__")[0]
g = {}
exec(src, g)
from itertools import combinations
def esymms(elems, mmax, p):
    pws = [sum(pow(x, j, p) for x in elems) % p for j in range(1, mmax+1)]
    e = [1]
    for j in range(1, mmax+1):
        s = 0
        for i in range(1, j+1):
            s += (-1)**(i-1) * e[j-i] * pws[i-1]
        e.append(s * pow(j, p-2, p) % p)
    return e[1:]
p, n, k = 11, 5, 2
best, _ = g['eps_profile_syndrome'](p, n, k)
H = g['smooth_domain'](p, n)
expected = {3: (3, 10, 10), 4: (2, 0, 2), 5: (1, 1, 1)}
for a in sorted(best, reverse=True):
    if a <= k: continue
    c = a - k
    lams = set()
    for A in combinations(H, a):
        e = esymms(list(A), max(c, 1), p)
        if all(e[j] == 0 for j in range(1, c)):
            lams.add((-e[0]) % p)
    stair = n - a + 1
    pred = min(p, max(stair, len(lams)))
    assert (stair, len(lams), pred) == expected[a] and pred == best[a], (a, stair, len(lams), best[a])
print("two-family law MATCHES at all rungs of the prime-n instance (11,5,2)  [OK]")
