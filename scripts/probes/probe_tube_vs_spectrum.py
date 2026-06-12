import random
from itertools import combinations
random.seed(371)
p, n, k = 12289, 8, 2
g = 8246
dom = [pow(g, i, p) for i in range(n)]
t_agree = 3
def interp2(i, j, line):
    xi, xj = dom[i], dom[j]
    b = (line[i] - line[j]) * pow(xi - xj, p-2, p) % p
    a = (line[i] - b*xi) % p
    return a, b
def explainable_with(line):
    out = []
    for i in range(n):
        for j in range(i+1, n):
            a, b = interp2(i, j, line)
            A = [t for t in range(n) if (a + b*dom[t]) % p == line[t]]
            if len(A) >= t_agree: out.append(tuple(A))
    return out
def joint_ok(T, u0, u1):
    for u in (u0, u1):
        ok = False
        for i in range(len(T)):
            for j in range(i+1, len(T)):
                a, b = interp2(T[i], T[j], u)
                if all((a + b*dom[t]) % p == u[t] for t in T):
                    ok = True; break
            if ok: break
        if not ok: return False
    return True
def bad_count(u0, u1):
    cnt = 0
    for gam in range(p):
        line = [(u0[i] + gam*u1[i]) % p for i in range(n)]
        found = False
        for A in explainable_with(line):
            for T in combinations(A, t_agree):
                if not joint_ok(list(T), u0, u1): found = True; break
            if found: break
        if found: cnt += 1
    return cnt
# regenerate trial 0 exactly
c = [ (random.randrange(p) + random.randrange(p)*x) % p for x in dom ]
eps = [0]*n
for i in random.sample(range(n), 2): eps[i] = random.randrange(1, p)
u1 = [(c[i] + eps[i]) % p for i in range(n)]
u0 = [pow(x, 3, p) * random.randrange(1, p) % p for x in dom]
cnt = bad_count(u0, u1)
print(f"tube stack bad = {cnt}")
print(f"u1 = affine{c[:2]}... + eps support {[i for i in range(n) if eps[i]]}")
print(f"u0 = scalar * x^3")
# controls: pure-affine direction (eps=0); pure-sparse direction; ladder with sparse u0
u1_aff = c
print("control: u0 = s*x^3, u1 = pure affine:", bad_count(u0, u1_aff))
u1_sp = eps
print("control: u0 = s*x^3, u1 = pure sparse-2:", bad_count(u0, u1_sp))
u0L = [pow(x, 3, p) for x in dom]; u1L = [pow(x, 2, p) for x in dom]
print("ladder (X^3, X^2):", bad_count(u0L, u1L))
