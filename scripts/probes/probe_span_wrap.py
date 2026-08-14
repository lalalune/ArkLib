import random
from sympy import isprime, primitive_root

# Genuinely-new wrap case: X^a + gamma X^b with k <= b < a <= n-1 (both freqs ABOVE
# the codeword window {0..k-1}). Shift X^{n-b} is ESSENTIAL (wraps the support).
# After shift by (n-b): exponents -> {a-b, 0} u {n-b .. n-b+k-1} (mod n). The support
# arc covering these from 0 has length = max(a-b, n-b+k-1 - n) ... the natural g:
#   g = X^{a-b} + C gamma - X^{n-b} * c    (c shifted up by n-b, but n-b+k-1 may exceed
#   ... actually X^{n-b}*c has degree n-b+k-1 which can be > a-b). The clean bound is
#   deg g <= max(a-b, n-b+k-1). Test agreement <= max(a-b, n-b+k-1)... but that can be
#   ~n (vacuous for spread). Instead test the TRUE span-1 and also a tighter natural one.
# We commit the literal no-wrap (Icc 0 a => <= a) which we proved holds. For the wrap
# theorem the honest clean bound to FORMALIZE: agreement <= a (since support subset {0..a}
# always, as a is the max exponent and a<=n-1). Validate <= a holds for k<=b<a.

def agreement(n, p, k, a, b, gamma, c):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    cnt = 0
    for x in mu:
        val = (pow(x, a, p) + gamma * pow(x, b, p)) % p
        cv = 0
        for i, ci in enumerate(c):
            cv = (cv + ci * pow(x, i, p)) % p
        if (val - cv) % p == 0:
            cnt += 1
    return cnt

random.seed(11)
cases = []
for n in [8, 16, 32]:
    t = n * n + 5
    while True:
        p = n * t + 1
        if isprime(p) and p > n ** 3:
            break
        t += 1
    cases.append((n, p))

tests = 0; fail_a = 0
for (n, p) in cases:
    for k in [2, 3]:
        for _ in range(150):
            if n - 1 < k + 1:
                continue
            a = random.randrange(k + 1, n)
            b = random.randrange(k, a)
            gamma = random.randrange(1, p)
            c = [random.randrange(0, p) for _ in range(k)]
            cnt = agreement(n, p, k, a, b, gamma, c)
            tests += 1
            if cnt > a:
                fail_a += 1
print("tests=%d fail(<=a)=%d" % (tests, fail_a))
