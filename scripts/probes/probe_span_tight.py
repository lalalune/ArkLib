import random
from sympy import isprime, primitive_root

# Check tightness: construct the BEST codeword (degree<k) for a given 2-sparse word
# and see how close max agreement gets to span-1. Brute over small fields.
# Agreement(c) = #{x in mu_n : x^a + gamma x^b = c(x)}.
# We can pick c to interpolate through any k points (degree<k => k coeffs => can hit
# k chosen target values), so agreement >= k is trivially reachable. The question is
# whether span-1 is the right ceiling (vs k+ something).

def arc_span(supp, n):
    s = sorted(set(x % n for x in supp))
    if len(s) == 1:
        return 1
    gaps = []
    for i in range(len(s)):
        gaps.append((s[(i + 1) % len(s)] - s[i]) % n)
    return n - max(gaps) + 1

def best_agreement(n, p, k, a, b, gamma):
    # vandermonde interpolation: choose which k points of mu_n to match exactly,
    # then count total agreement. Try matching the k points that give max total.
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    vals = [(pow(x, a, p) + gamma * pow(x, b, p)) % p for x in mu]
    best = 0
    # interpolate a degree<k poly through k chosen nodes; count matches over all mu
    from itertools import combinations
    if n > 24:
        # too big to brute all combos; sample
        idxsets = [tuple(random.sample(range(n), k)) for _ in range(400)]
    else:
        idxsets = list(combinations(range(n), k))
    for idx in idxsets:
        xs = [mu[i] for i in idx]
        ys = [vals[i] for i in idx]
        # solve vandermonde for coeffs c_0..c_{k-1}
        # build matrix
        M = [[pow(xs[r], cidx, p) for cidx in range(k)] for r in range(k)]
        coeffs = solve_mod(M, ys, p)
        if coeffs is None:
            continue
        cnt = 0
        for x in mu:
            cv = 0
            for cidx, ci in enumerate(coeffs):
                cv = (cv + ci * pow(x, cidx, p)) % p
            v = (pow(x, a, p) + gamma * pow(x, b, p)) % p
            if (v - cv) % p == 0:
                cnt += 1
        best = max(best, cnt)
    return best

def solve_mod(M, y, p):
    n = len(M)
    A = [row[:] + [y[i]] for i, row in enumerate(M)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], p - 2, p)
        A[col] = [(v * inv) % p for v in A[col]]
        for r in range(n):
            if r != col and A[r][col] % p != 0:
                f = A[r][col]
                A[r] = [(A[r][c] - f * A[col][c]) % p for c in range(n + 1)]
    return [A[i][n] % p for i in range(n)]

random.seed(3)
for n in [8, 16]:
    t = n * n + 5
    while True:
        p = n * t + 1
        if isprime(p) and p > n ** 3:
            break
        t += 1
    g = primitive_root(p)
    for k in [2, 3]:
        # consecutive-top a=n-1,b=n-2 (span = k+1), gapped a=n-1,b=n-j
        for (a, b, label) in [(n - 1, n - 2, "consec"), (n - 1, n // 2, "gap=n/2"), (n - 1, 0, "gap")]:
            gamma = 1
            ba = best_agreement(n, p, k, a, b, gamma)
            supp = set([a, b]) | set(range(k))
            span = arc_span(supp, n)
            print("n=%d k=%d %s a=%d b=%d : best_agreement=%d  span-1=%d  %s"
                  % (n, k, label, a, b, ba, span - 1, "TIGHT" if ba == span - 1 else ("OK" if ba <= span - 1 else "VIOLATION")))
