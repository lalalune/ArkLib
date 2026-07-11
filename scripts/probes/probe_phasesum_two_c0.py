import itertools, cmath, random

def phaseSum(u, m, r, c):
    total = 0+0j
    for X in itertools.product(range(m), repeat=r):
        if all(x != 0 for x in X) and (sum(X) % m) == c:
            p = 1+0j
            for x in X:
                p *= u[x]
            total += p
    return total

# Test: for a conjugate-symmetric unit-phase vector (u[-a] = conj(u[a])),
# phaseSum u 2 0 = sum_{a!=0} u[a]*u[-a] = sum_{a!=0} |u[a]|^2 = m-1 (REAL, positive).
random.seed(7)
for m in [3, 5, 7, 9, 11, 15]:
    # build conjugate-symmetric unit phases: pick phases for 1..(m-1)//2, mirror
    u = [0j]*m
    u[0] = cmath.exp(2j*cmath.pi*random.random())  # u[0] arbitrary unit
    for a in range(1, m//2 + 1):
        ph = cmath.exp(2j*cmath.pi*random.random())
        u[a] = ph
        u[(m-a) % m] = ph.conjugate()
    ps0 = phaseSum(u, m, 2, 0)
    # claim ps0 == m-1
    print(f"m={m} phaseSum_2_0={ps0:.6f}  claim(m-1)={m-1}  match={abs(ps0-(m-1))<1e-9}")
