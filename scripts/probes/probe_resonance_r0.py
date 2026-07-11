import itertools, cmath, random

def phaseSum(u, r, c, m):
    total = 0 + 0j
    for X in itertools.product(range(m), repeat=r):
        if all(xi != 0 for xi in X) and (sum(X) % m) == c:
            p = 1 + 0j
            for xi in X:
                p *= u[xi]
            total += p
    return total

for m in [5, 7, 11]:
    u = [cmath.exp(2j * cmath.pi * random.random()) for _ in range(m)]
    for c in range(m):
        val = phaseSum(u, 0, c, m)
        expected = (1 + 0j) if c == 0 else (0 + 0j)
        assert abs(val - expected) < 1e-12, (m, c, val, expected)
    T0 = sum(abs(phaseSum(u, 0, c, m)) ** 2 for c in range(m))
    assert abs(T0 - 1.0) < 1e-12, (m, T0)
    print(f"m={m}: phaseSum u 0 c = [c==0?1:0] OK, resonanceMoment u 0 = {T0:.6f} OK")
print("ALL PASS: r=0 base case confirmed exact.")
