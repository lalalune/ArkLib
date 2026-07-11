import random
from sympy import isprime, primitive_root

# Validate the explicit bound for X^a + gamma X^b vs deg<k codeword, a>b,
# via the shift X^{n-b}: support {a,b}u{0..k-1} -> {a-b, 0}u{n-b .. n-b+k-1}.
# Cleaner: shift X^{n-b} maps exponent e -> e + (n-b) mod n. Choose the window so the
# claimed bound is max(a-b, k-1) ... actually test the in-file-style g-degree bound.
# We test the agreement <= ((a-b) + k - 1) when b < a and the codeword window {0..k-1}
# sits below b? Let's just test the GENERAL arc-span bound = span-1 (already validated)
# but specifically for a,b with b possibly nonzero and b < k (codeword overlaps).

def arc_span(supp, n):
    s = sorted(set(x % n for x in supp))
    if len(s) == 1:
        return 1
    gaps = []
    for i in range(len(s)):
        gaps.append((s[(i + 1) % len(s)] - s[i]) % n)
    return n - max(gaps) + 1

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

random.seed(7)
cases = []
for n in [8, 16, 32]:
    t = n * n + 5
    while True:
        p = n * t + 1
        if isprime(p) and p > n ** 3:
            break
        t += 1
    cases.append((n, p))

# Specifically: a in {k..n-1}, b in {0..k-1} (b inside the codeword window), a>b.
# Claim shift X^{n-b}... simpler claim we PROVE in Lean:
#   for a >= k, b < k:  shift X^{n-b} -> g = X^{a-b}+ C gamma - X^{n-b}*c (deg from wrap)
# instead validate generic span-1 holds AND that for b<k<=a, agreement <= a-b ... test both.
tests = 0; fail_span = 0; fail_ab = 0
for (n, p) in cases:
    for k in [2, 3, 4]:
        for _ in range(120):
            a = random.randrange(k, n)
            b = random.randrange(0, n)
            if b >= a:
                continue
            gamma = random.randrange(1, p)
            c = [random.randrange(0, p) for _ in range(k)]
            cnt = agreement(n, p, k, a, b, gamma, c)
            supp = set([a, b]) | set(range(k))
            span = arc_span(supp, n)
            tests += 1
            if cnt > span - 1:
                fail_span += 1
            # the literal (no-wrap) arc bound: support all in Icc 0 a -> agreement <= a
            if cnt > a:  # since support subset {0..a} (b<a, k-1<=a-1<a, a)
                fail_ab += 1
print("tests=%d fail(span-1)=%d fail(<=a literal)=%d" % (tests, fail_span, fail_ab))
