import itertools
from sympy import symbols, ZZ, cyclotomic_poly, resultant, Poly

x = symbols('x')

def vlam(n, terms):
    Phi = cyclotomic_poly(n, x)
    Dp = 0
    for (eps, a) in terms:
        Dp = Dp + eps * x**(a % n)
    Dpoly = Poly(Dp, x, domain=ZZ)
    Phipoly = Poly(Phi, x, domain=ZZ)
    N = int(resultant(Dpoly, Phipoly))
    if N == 0:
        return None
    v2 = 0
    m = abs(N)
    while m % 2 == 0:
        m //= 2
        v2 += 1
    return v2

# Tightness: count how often each (s0 parity, s1 parity) class occurs and the v distribution.
# Want to confirm: among s0 even cases, s1 odd => v==1 EXACTLY (never >=2), and s1 even => v>=2.
for n in [8, 16]:
    print("=== n=%d ===" % n)
    classes = {}  # (s0%2, s1%2) -> list of v
    exps = list(range(n))
    for k in [2, 3, 4]:
        for combo in itertools.combinations(exps, k):
            for signs in itertools.product([1, -1], repeat=k):
                terms = list(zip(signs, combo))
                v = vlam(n, terms)
                if v is None:
                    continue
                s0 = sum(e for e, a in terms)
                s1 = sum(e * a for e, a in terms)
                key = (s0 % 2, s1 % 2)
                classes.setdefault(key, []).append(v)
    for key in sorted(classes):
        vs = classes[key]
        print("  (s0%%2,s1%%2)=%s  count=%d  min_v=%d  max_v=%d  v>=2_count=%d" % (
            key, len(vs), min(vs), max(vs), sum(1 for v in vs if v >= 2)))
