import itertools
from sympy import symbols, ZZ, cyclotomic_poly, resultant, Poly, binomial

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

# graded moments sigma_j = sum eps_i * C(a_i, j). The depth-ell congruence claims
#   D == sum_{j<ell} sigma_j * t^j   (mod I^ell),   t = zeta - 1, ζ^a=(1+t)^a=sum_j C(a,j) t^j.
# The INTEGER gate hypothesis to test (depth 3): v_lambda(D) >= 3  <=>  sigma_0,sigma_1,sigma_2 all even.
def sigma(terms, j):
    return sum(e * int(binomial(a, j)) for e, a in terms)

for n in [8, 16]:
    print("=== n=%d ===" % n)
    viol3 = 0
    checked = 0
    classes = {}
    exps = list(range(n))
    for k in [2, 3, 4]:
        for combo in itertools.combinations(exps, k):
            for signs in itertools.product([1, -1], repeat=k):
                terms = list(zip(signs, combo))
                v = vlam(n, terms)
                if v is None:
                    continue
                checked += 1
                s0 = sigma(terms, 0) % 2
                s1 = sigma(terms, 1) % 2
                s2 = sigma(terms, 2) % 2
                pred3 = (s0 == 0 and s1 == 0 and s2 == 0)
                act3 = (v >= 3)
                if pred3 != act3:
                    viol3 += 1
                key = (s0, s1, s2)
                classes.setdefault(key, []).append(v)
    print("  checked=%d  depth3(s0,s1,s2 even)_viol=%d" % (checked, viol3))
    for key in sorted(classes):
        vs = classes[key]
        print("   (s0,s1,s2)=%s count=%d min_v=%d max_v=%d ge3=%d" % (
            key, len(vs), min(vs), max(vs), sum(1 for v in vs if v >= 3)))
