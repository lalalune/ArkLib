import itertools, cmath, math, random
from collections import defaultdict

# Two questions about the agreement off-diagonal O(r) := T(r) - (m-1)^r (real, just proven):
# Q1 (gauge): is agreementDouble invariant under u -> c*u for unit c?  (each term has r conj + r unconj
#     factors -> c^{-r} c^{r} = 1, so YES expected). Confirm numerically.
# Q2 (SIGN): can O(r).re be NEGATIVE for some unit-modulus u?  i.e. can the off-diagonal interfere
#     DESTRUCTIVELY below the Wick floor (m-1)^r?  If O >= 0 always, that's a Lane-3 floor lock.
#     If O can be < 0, that's a different (and important) structural fact.

def Tr(m, r, u):
    nz = [a for a in range(m) if a != 0]
    fib = defaultdict(complex)
    for X in itertools.product(nz, repeat=r):
        fib[sum(X) % m] += math.prod(u[a] for a in X)
    return sum(abs(v) ** 2 for v in fib.values())

random.seed(7)
min_off = 1e9
max_gauge_err = 0.0
neg_examples = 0
for m in [3, 4, 5, 7]:
    for r in [1, 2, 3]:
        wick = (m - 1) ** r
        for trial in range(2000):
            u = {0: 0j}
            for a in range(1, m):
                u[a] = cmath.exp(1j * random.uniform(0, 2 * math.pi))
            T = Tr(m, r, u)
            off = T - wick
            min_off = min(min_off, off)
            if off < -1e-9:
                neg_examples += 1
            # gauge check: rotate by random unit c
            c = cmath.exp(1j * random.uniform(0, 2 * math.pi))
            uc = {0: 0j, **{a: c * u[a] for a in range(1, m)}}
            Tc = Tr(m, r, uc)
            max_gauge_err = max(max_gauge_err, abs(Tc - T))

print(f"Q1 gauge: max |T(c*u) - T(u)| over rotations = {max_gauge_err:.2e}  (0 => gauge-invariant)")
print(f"Q2 sign:  min off-diagonal O(r)=T-(m-1)^r over all unit u = {min_off:.4f}")
print(f"          # trials with O < 0: {neg_examples}")
print("VERDICT Q2:", "O >= 0 always (Wick floor holds for ALL unit u) — Lane-3 floor lock"
      if min_off >= -1e-9 else "O can be NEGATIVE — off-diagonal interferes below Wick floor")
