import itertools, cmath, math
from collections import defaultdict

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

# For 4 roots of unity a,b,c,d (|x|=1):
#   conj(e1) = e3/e4   (e3 = conj(e1)*e4)
#   conj(e2) = e2/e4   (e2 = conj(e2)*e4, i.e. e2 self-conjugate up to e4)
#   conj(e3) = e1/e4
# Check identities exactly + whether (e1,e4) determines e2 (i.e. does e2 vary for fixed e1,e4?).
for n in [4, 8, 16]:
    R = roots(n)
    err3 = 0.0; err2 = 0.0
    by_e1e4 = defaultdict(set)
    cnt = 0
    for t in itertools.combinations_with_replacement(range(n), 4):
        e1, e2, e3, e4 = esymm([R[i] for i in t], 4)
        err3 = max(err3, abs(e3 - conj(e1)*e4))
        err2 = max(err2, abs(e2 - conj(e2)*e4))
        key = (round(e1.real,6), round(e1.imag,6), round(e4.real,6), round(e4.imag,6))
        by_e1e4[key].add((round(e2.real,6), round(e2.imag,6)))
        cnt += 1
    # how many (e1,e4) classes have >1 distinct e2?
    multi_e2 = sum(1 for s in by_e1e4.values() if len(s) > 1)
    print(f"n={n:3d}: e3=conj(e1)*e4 err={err3:.1e} | e2=conj(e2)*e4 err={err2:.1e} | "
          f"(e1,e4)-classes with multiple e2 values: {multi_e2}/{len(by_e1e4)} ({cnt} tuples)")
