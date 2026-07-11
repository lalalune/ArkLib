import cmath, math

def order(a, p):
    o = 1; cur = a % p
    while cur != 1:
        cur = (cur * a) % p; o += 1
    return o

def gen_of(p):
    for a in range(2, p):
        if order(a, p) == p - 1:
            return a
    return None

def subgroup(p, n, gen):
    h = pow(gen, (p - 1) // n, p)
    sub = []; cur = 1
    for _ in range(n):
        sub.append(cur); cur = (cur * h) % p
    return sub

def E1E2(p, n, gen):
    sub = subgroup(p, n, gen)
    e1 = 0.0; e2 = 0.0
    for b in range(p):
        s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in sub)
        m = abs(s) ** 2
        e1 += m; e2 += m * m
    return e1 / p, e2 / p

# exact iff:  A_2 <= 3n A_1  <=>  E_2 <= 3n^2 + n^3(n-3)/p
# verify the iff holds cell-by-cell (both sides agree on VIOL/OK)
p = 40961
g = gen_of(p)
print("verify EXACT iff: [A2<=3n A1] == [E2 <= 3n^2 + n^3(n-3)/p]")
for n in [8, 16, 32, 64, 128, 256, 512]:
    if (p-1) % n: continue
    E1, E2 = E1E2(p, n, g)
    A1 = E1 - n**2/p; A2 = E2 - n**4/p
    lhs = (A2 <= 3*n*A1 + 1e-6)
    thr = 3*n*n + n**3*(n-3)/p
    rhs = (E2 <= thr + 1e-6)
    print("  n=%4d  E2=%.2f thr=%.2f  step_holds=%s  E2<=thr=%s  AGREE=%s"
          % (n, E2, thr, lhs, rhs, lhs == rhs))
