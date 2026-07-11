import random
from sympy import isprime, primitive_root

# Validate the span bound for a GENERAL t-sparse word sum_i gamma_i X^{a_i}
# vs deg<k codeword. support = {a_0,...,a_{t-1}} u {0..k-1}.
# Claim: agreement on mu_n <= (literal span from 0) - 1 = max_exponent
#        (when support subset {0..A}, A=max(a_i)) -> agreement <= A.
# And the cyclic-arc span bound: agreement <= span-1.

def arc_span(supp, n):
    s = sorted(set(x % n for x in supp))
    if len(s) == 1:
        return 1
    gaps = []
    for i in range(len(s)):
        gaps.append((s[(i + 1) % len(s)] - s[i]) % n)
    return n - max(gaps) + 1

def agreement(n, p, k, exps, coeffs, c):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    cnt = 0
    for x in mu:
        val = 0
        for e, gm in zip(exps, coeffs):
            val = (val + gm * pow(x, e, p)) % p
        cv = 0
        for i, ci in enumerate(c):
            cv = (cv + ci * pow(x, i, p)) % p
        if (val - cv) % p == 0:
            cnt += 1
    return cnt

random.seed(13)
cases = []
for n in [8, 16, 32]:
    t = n * n + 5
    while True:
        p = n * t + 1
        if isprime(p) and p > n ** 3:
            break
        t += 1
    cases.append((n, p))

tests = 0; fail_span = 0; fail_A = 0
for (n, p) in cases:
    for k in [2, 3]:
        for tsp in [2, 3, 4]:
            for _ in range(60):
                exps = random.sample(range(n), tsp)
                coeffs = [random.randrange(1, p) for _ in range(tsp)]
                c = [random.randrange(0, p) for _ in range(k)]
                cnt = agreement(n, p, k, exps, coeffs, c)
                supp = set(exps) | set(range(k))
                span = arc_span(supp, n)
                A = max(supp)
                tests += 1
                if cnt > span - 1:
                    fail_span += 1
                if cnt > A:
                    fail_A += 1
print("tests=%d fail(span-1)=%d fail(<=A literal)=%d" % (tests, fail_span, fail_A))
