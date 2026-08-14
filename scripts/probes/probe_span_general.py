import random
from sympy import isprime, primitive_root

# Validate the GENERAL span bound for an arbitrary 2-sparse word X^a + gamma*X^b
# vs a degree-<k codeword, agreement on mu_n:
#   agreement <= (span of support arc mod n) - 1
# support = {a,b} union {0..k-1}; span = number of points in the minimal
# contiguous arc (mod n) covering the support = n - (largest cyclic gap).

def arc_span(supp, n):
    s = sorted(set(x % n for x in supp))
    if len(s) == 1:
        return 1
    gaps = []
    for i in range(len(s)):
        nxt = s[(i + 1) % len(s)]
        cur = s[i]
        gaps.append((nxt - cur) % n)
    return n - max(gaps) + 1

def agreement(n, p, k, a, b, gamma, c_coeffs):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    cnt = 0
    for x in mu:
        val = (pow(x, a, p) + gamma * pow(x, b, p)) % p
        cv = 0
        for i, ci in enumerate(c_coeffs):
            cv = (cv + ci * pow(x, i, p)) % p
        if (val - cv) % p == 0:
            cnt += 1
    return cnt

random.seed(1)
cases = []
for n in [8, 16, 32]:
    t = n * n + 5
    while True:
        p = n * t + 1
        if isprime(p) and p > n ** 3:
            break
        t += 1
    cases.append((n, p))

tests = 0
fails = 0
examples = []
tight = 0
for (n, p) in cases:
    for k in [2, 3, 4]:
        for _ in range(80):
            a = random.randrange(n)
            b = random.randrange(n)
            if a == b:
                continue
            gamma = random.randrange(1, p)
            c = [random.randrange(0, p) for _ in range(k)]
            cnt = agreement(n, p, k, a, b, gamma, c)
            supp = set([a, b]) | set(range(k))
            span = arc_span(supp, n)
            tests += 1
            if cnt > span - 1:
                fails += 1
                if len(examples) < 10:
                    examples.append((n, p, k, a, b, cnt, span))
            if cnt == span - 1:
                tight += 1

print("tests=%d fails(cnt>span-1)=%d tight(cnt==span-1)=%d" % (tests, fails, tight))
for e in examples:
    print("FAIL n=%d p=%d k=%d a=%d b=%d cnt=%d span=%d" % e)
