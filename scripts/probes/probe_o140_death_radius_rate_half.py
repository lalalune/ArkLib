# O140: the adjacent-pair death radius is rate-UNIVERSAL at constraint depth 2.
# Companion to O139 (rate 1/4). Rate 1/2 (n=16, k=8), window = (Johnson 0.2929, capacity 0.5).
# census(a) = #{-e1(A) : A in C(mu_16, a), e2(A)=...=e_{a-8}(A)=0}, delta = 1 - a/16.
# Verdicts (exact, all four fields with 16 | p-1):
#  a=9  (delta=.4375, 0 constraints, a=k+1): all C(16,9)=11440 subsets qualify; census
#     SATURATES the field (= p) at p in {17,97,113,193} - same eps_ca = 1 saturation
#     above Johnson as O139's a=5 row.
#  a=10 (delta=.375, 1 constraint e2=0): field-dependent, ~n-scale census:
#     (p,#qual,census) = (17,432,17), (97,32,16), (113,64,32), (193,32,32).
#  a=11 (delta=.3125, 2 constraints e2=e3=0): EMPTY at EVERY p tested - INCLUDING p=17
#     (which retained 32 qualifying subsets at rate 1/4). Death radius
#     delta_death(16,8) in (0.3125, 0.375].
#
# Reading: at BOTH measured rates the adjacent-pair family dies at exactly TWO vanishing
# power sums, i.e. delta_death(n,k) in (1-(k+3)/n, 1-(k+2)/n] = (capacity - 3/n,
# capacity - 2/n]: the family's bad strip is capacity - Theta(1/n), *narrower* at toy
# scale than the KKH26 Theta(1/log n) strip. If the adjacent-pair extremality conjecture
# (O138) holds at small n while KKH26's m>1 fiber shapes dominate at large n, the two
# families MUST cross over in n - locating that crossover is now a concrete probe-able
# question that directly shapes delta*.
from itertools import combinations


def subgroup(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            elems.add(x)
        if len(elems) == p - 1:
            gen = pow(g, (p - 1) // n, p)
            H = sorted(set(pow(gen, i, p) for i in range(n)))
            assert len(H) == n
            return H


def esymms(A, m, p):
    pws = [sum(pow(a, j, p) for a in A) % p for j in range(1, m + 1)]
    e = [1]
    for j in range(1, m + 1):
        s = 0
        for i in range(1, j + 1):
            s += (-1) ** (i - 1) * e[j - i] * pws[i - 1]
        e.append(s * pow(j, p - 2, p) % p)
    return e[1:]


n, k = 16, 8
expected = {
    17: [(9, 11440, 17), (10, 432, 17), (11, 0, 0)],
    97: [(9, 11440, 97), (10, 32, 16), (11, 0, 0)],
    113: [(9, 11440, 113), (10, 64, 32), (11, 0, 0)],
    193: [(9, 11440, 193), (10, 32, 32), (11, 0, 0)],
}
for p in (17, 97, 113, 193):
    H = subgroup(p, n)
    row = []
    for a in (9, 10, 11):
        ncon = a - k
        cnt, lams = 0, set()
        for A in combinations(H, a):
            e = esymms(A, ncon, p)
            if all(v == 0 for v in e[1:ncon]):
                cnt += 1
                lams.add((-e[0]) % p)
        row.append((a, cnt, len(lams)))
    assert row == expected[p], (p, row)
    print(f"p={p}: (a, #qualifying, census) = {row}  [OK]")
print("O140 rate-1/2 death-radius verdicts reproduced")
