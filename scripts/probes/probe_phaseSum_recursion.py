import itertools, cmath, random
def phaseSum(u, m, r, c):
    tot = 0+0j
    nz = [a for a in range(m) if a != 0]
    for X in itertools.product(nz, repeat=r):
        if sum(X) % m == c:
            p = 1+0j
            for xi in X: p *= u[xi]
            tot += p
    return tot

def check(m, r, seed=0):
    random.seed(seed)
    u = [cmath.exp(2j*cmath.pi*random.random()) for _ in range(m)]
    nz = [a for a in range(m) if a != 0]
    maxerr = 0.0
    for c in range(m):
        lhs = phaseSum(u, m, r+1, c)
        rhs = 0+0j
        for a in nz:
            rhs += u[a] * phaseSum(u, m, r, (c-a) % m)
        maxerr = max(maxerr, abs(lhs-rhs))
    return maxerr

for m in [3,5,7,9]:
    for r in [1,2,3]:
        e = check(m, r)
        print(f"m={m} r={r}: max|lhs-rhs| = {e:.2e}")
