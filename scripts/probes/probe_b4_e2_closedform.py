import itertools, cmath, math

def roots(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def esymm(vals, h):
    es = [0j]*(h+1); es[0] = 1+0j
    for v in vals:
        for k in range(h, 0, -1):
            es[k] += es[k-1]*v
    return es[1:]

def conj(z):
    return complex(z.real, -z.imag)

# Hypothesis: when e1 != 0, is e2 determined by e1, e4 via a clean identity?
# Newton power sums: p1=e1; p2=e1^2-2e2; p3=e1^3-3e1 e2+3e3; ...
# Conjugation: p_k(1/x) = conj(p_k). For roots of unity, sum 1/x_i^k = conj(sum x_i^k) = conj(p_k).
# Also e_{4-j} = e4 * conj(e_j) (Vieta reciprocal: product * elem-sym of inverses).
#   e3 = e4*conj(e1); e2 = e4*conj(e2); e1 = e4*conj(e3).
# e2 = e4*conj(e2) is ONE complex equation. Writing e2 = u: u = e4*conj(u).
# If e4 = exp(i*phi), then u must satisfy u*exp(-i phi/2) is REAL (u lies on the line through
# origin at angle phi/2). That's a 1-real-parameter family, NOT determined by e4 alone.
# So e2 is NOT closed-form in (e1,e4). The multiset determination must use e1!=0 more globally.
# TEST: does (e1, e4) + the constraint determine e2 uniquely when e1 != 0? Count distinct e2
# per (e1,e4) restricted to e1 != 0.
from collections import defaultdict
for n in [8, 16]:
    R = roots(n)
    by = defaultdict(set)
    for t in itertools.combinations_with_replacement(range(n), 4):
        e1, e2, e3, e4 = esymm([R[i] for i in t], 4)
        if abs(e1) < 1e-7:
            continue
        key = (round(e1.real,6), round(e1.imag,6), round(e4.real,6), round(e4.imag,6))
        by[key].add((round(e2.real,5), round(e2.imag,5)))
    multi = {k: v for k, v in by.items() if len(v) > 1}
    print(f"n={n}: e1!=0 (e1,e4)-classes with multiple e2: {len(multi)}/{len(by)}")
    # also test if (e1, e2, e4) determines multiset (the honest hypothesis set)
