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
def T(u, m, r):
    return sum(abs(phaseSum(u,m,r,c))**2 for c in range(m))
random.seed(1)
print("check T(r+1) <= (m-1)^2 * T(r) for unit phases:")
for m in [3,5,7]:
    u=[cmath.exp(2j*cmath.pi*random.random()) for _ in range(m)]
    for r in [1,2,3]:
        lhs=T(u,m,r+1); rhs=(m-1)**2*T(u,m,r)
        print(f" m={m} r={r}: T(r+1)={lhs:.3f}  (m-1)^2 T(r)={rhs:.3f}  holds={lhs<=rhs+1e-9}")
