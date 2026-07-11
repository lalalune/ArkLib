import itertools
from sympy import symbols, ZZ, cyclotomic_poly, resultant, Poly

x = symbols('x')

def vlam_of_signed(n, terms):
    Phi = cyclotomic_poly(n, x)
    Dp = 0
    for (eps, a) in terms:
        Dp = Dp + eps * x**(a % n)
    Dpoly = Poly(Dp, x, domain=ZZ)
    Phipoly = Poly(Phi, x, domain=ZZ)
    N = int(resultant(Dpoly, Phipoly))
    if N == 0:
        return None, 0
    v2 = 0
    m = abs(N)
    while m % 2 == 0:
        m //= 2
        v2 += 1
    return v2, abs(N)

def sigma0(terms):
    return sum(e for e, a in terms)

def sigma1(terms):
    return sum(e * a for e, a in terms)

for n in [8, 16]:
    print("=== n=%d (mu=%d) ===" % (n, n.bit_length() - 1))
    viol_d1 = 0
    viol_d2 = 0
    checked = 0
    found = []
    exps = list(range(n))
    for k in [2, 3, 4]:
        for combo in itertools.combinations(exps, k):
            for signs in itertools.product([1, -1], repeat=k):
                terms = list(zip(signs, combo))
                v, N = vlam_of_signed(n, terms)
                if v is None:
                    continue
                checked += 1
                s0 = sigma0(terms)
                s1 = sigma1(terms)
                d1_pred = (s0 % 2 == 0)
                d1_act = (v >= 1)
                if d1_pred != d1_act:
                    viol_d1 += 1
                d2_pred = (s0 % 2 == 0) and (s1 % 2 == 0)
                d2_act = (v >= 2)
                if d2_pred != d2_act:
                    viol_d2 += 1
                    if len(found) < 8:
                        found.append((terms, s0, s1, v))
    print("  checked=%d  depth1_viol=%d  depth2(s0&s1 even)_viol=%d" % (checked, viol_d1, viol_d2))
    for ex in found:
        print("   CEX:", ex)
