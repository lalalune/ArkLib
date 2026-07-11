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

def eta_abs2(b, p, sub):
    s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in sub)
    return abs(s) ** 2

def step_r1(p, n, gen):
    # subgroup is unique (cyclic group has unique subgroup of each order) -> gen choice irrelevant,
    # but verify by computing the actual set. returns A2/A1 and 3n.
    sub = subgroup(p, n, gen)
    assert len(set(sub)) == n
    A1 = 0.0; A2 = 0.0
    for b in range(1, p):
        m = eta_abs2(b, p, sub)
        A1 += m; A2 += m * m
    A1 /= p; A2 /= p
    return A2 / A1, 3.0 * n

# confirm (40961,64) violation across generators (should be identical - unique subgroup)
p = 40961
g1 = gen_of(p)
# find a different generator
g2 = None
for a in range(g1 + 1, p):
    if order(a, p) == p - 1:
        g2 = a; break
for g in [g1, g2]:
    r, bd = step_r1(p, 64, g)
    print("p=40961 n=64 gen=%5d  A2/A1=%.4f  3n=%d  ratio=%.4f  %s"
          % (g, r, bd, r / bd, "VIOL" if r > bd else "OK"))

# scan n for p=40961 to locate the violation band vs beta
print("\nscan p=40961, n=2^a:")
for n in [8, 16, 32, 64, 128, 256, 512, 1024]:
    if (p - 1) % n != 0:
        print("  n=%d skip (n nmid p-1)" % n); continue
    r, bd = step_r1(p, n, g1)
    beta = math.log(p) / math.log(n)
    print("  n=%4d beta=%.2f  A2/A1=%9.3f  3n=%5d  ratio=%.4f %s"
          % (n, beta, r, bd, r / bd, "VIOL" if r > bd else "OK"))
