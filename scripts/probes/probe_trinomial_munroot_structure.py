# Probe: SHARP mu_n-incidence law for genuine 3-term (trinomial) directions on thin mu_n.
# in-tree bound is the bare degree i-k. binomial got gcd(|i-j|,n) (a divisor of n). Question:
# is there a cyclotomic-divisor structural cap for trinomials? Test two candidates:
#   (A) inc <= gcd(i-j, j-k, n)   [gcd of exponent-diffs with n]
#   (B) inc <= gcd(i-k, n)        [outer span gcd with n]
# PROPER thin subgroup mu_n (order n), NEVER n=q-1. multi-prime incl p>n^3 + Fermat.
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

tot = 0; viol_A = 0; viol_B = 0
from collections import defaultdict
mx = defaultdict(int)
exact_A = 0  # how often inc EQUALS gcd(i-j,j-k,n)

for n in [4, 8, 16]:
    cands = [p for p in range(n + 1, 20000)
             if isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= 2]
    picks = cands[:3]
    big = [p for p in cands if p > n ** 3]
    if big:
        picks.append(big[0])
    if n == 16 and 65537 in cands:
        picks.append(65537)
    if n in (4, 8) and 257 in cands:
        picks.append(257)
    for p in picks:
        S = mu_n(p, n)
        if S is None:
            continue
        for k, j, i in itertools.combinations(range(0, min(n + 2, 9)), 3):
            for c1 in S[:4]:
                for c2 in S[:4]:
                    if c1 == 0 or c2 == 0:
                        continue
                    roots = [x for x in S if x != 0 and
                             (pow(x, i, p) - c1 * pow(x, j, p) - c2 * pow(x, k, p)) % p == 0]
                    inc = len(roots)
                    if inc == 0:
                        continue
                    tot += 1
                    gA = math.gcd(math.gcd(i - j, j - k), n)
                    gB = math.gcd(i - k, n)
                    if inc > gA:
                        viol_A += 1
                    if inc > gB:
                        viol_B += 1
                    if inc == gA:
                        exact_A += 1
                    mx[n] = max(mx[n], inc)

print("total nonzero-incidence trinomial configs:", tot)
print("violations of (A) inc <= gcd(i-j, j-k, n):", viol_A)
print("violations of (B) inc <= gcd(i-k, n):     ", viol_B)
print("times inc == gcd(i-j,j-k,n) exactly:      ", exact_A)
print("max incidence per n (compare to n):       ", dict(mx))
