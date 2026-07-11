# Why does inc | n hold for trinomial mu_n-incidence? Test: is the root set a union of
# cosets of mu_d for some d | n (i.e. closed under mult by a subgroup)? Or is inc|n an
# artifact of small samples? Push to larger configs + check the stabilizer subgroup.
import itertools, math
from sympy import isprime

def mu_gen(p, n):
    if (p - 1) % n != 0:
        return None
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    for g in range(2, p):
        if order(g) == p - 1:
            return pow(g, (p - 1) // n, p)
    return None

def mu_n(p, n):
    h = mu_gen(p, n)
    if h is None:
        return None
    s = []; x = 1
    for _ in range(n):
        s.append(x); x = (x * h) % p
    return sorted(set(s))

tot = 0; divn_viol = 0; nontrivial_stab = 0
counter_examples = []
for n in [4, 8, 16, 32]:
    cands = [p for p in range(n + 1, 80000)
             if isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= 2]
    picks = cands[:4]
    big = [p for p in cands if p > n ** 3]
    if big:
        picks.append(big[0])
    for p in picks:
        S = mu_n(p, n)
        if S is None:
            continue
        Sset = set(S)
        for k, j, i in itertools.combinations(range(0, min(n + 2, 10)), 3):
            for c1 in S[:5]:
                for c2 in S[:5]:
                    roots = [x for x in S if x != 0 and
                             (pow(x, i, p) - c1 * pow(x, j, p) - c2 * pow(x, k, p)) % p == 0]
                    inc = len(roots)
                    if inc == 0:
                        continue
                    tot += 1
                    if n % inc != 0:
                        divn_viol += 1
                        if len(counter_examples) < 8:
                            counter_examples.append((n, p, i, j, k, c1, c2, inc, sorted(roots)))
print("total configs:", tot)
print("inc | n violations:", divn_viol)
if counter_examples:
    print("COUNTEREXAMPLES (inc does NOT divide n):")
    for ce in counter_examples:
        print("  ", ce)
else:
    print("inc | n held in ALL", tot, "configs across n in {4,8,16,32}.")
