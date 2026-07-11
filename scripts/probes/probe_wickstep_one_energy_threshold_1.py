import cmath, math

def order(a, p):
    o = 1
    cur = a % p
    while cur != 1:
        cur = (cur * a) % p
        o += 1
    return o

def subgroup(p, n):
    gen = None
    for a in range(2, p):
        if order(a, p) == p - 1:
            gen = a
            break
    h = pow(gen, (p - 1) // n, p)
    sub = []
    cur = 1
    for _ in range(n):
        sub.append(cur)
        cur = (cur * h) % p
    return sub

def eta_abs2(b, p, sub):
    s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in sub)
    return abs(s) ** 2

def test(p, n):
    sub = subgroup(p, n)
    A1 = 0.0
    A2 = 0.0
    for b in range(1, p):
        m = eta_abs2(b, p, sub)
        A1 += m
        A2 += m * m
    A1 /= p
    A2 /= p
    return A1, A2, (A2 / A1 if A1 > 1e-9 else float('inf'))

pairs = [(193,8),(257,8),(257,16),(7681,8),(7681,16),(7681,32),
         (12289,8),(12289,16),(12289,32),(40961,8),(40961,16),(40961,32),
         (786433,8),(786433,16),(786433,32),(786433,64)]

ratios = []
for p, n in pairs:
    if (p - 1) % n != 0:
        print("SKIP p=%d n=%d" % (p, n))
        continue
    A1, A2, r = test(p, n)
    beta = math.log(p) / math.log(n)
    # The r=1 Wick cross-step is A_2 <= 3*|G|*A_1, i.e. A2/A1 <= 3n (NOT <= 3).
    bound = 3.0 * n
    flag = "OK" if r <= bound + 1e-6 else "VIOLATES"
    ratios.append(r / bound)
    print("p=%7d n=%3d beta=%.2f A1=%.4f A2=%.4f A2/A1=%.4f /3n=%.4f %s"
          % (p, n, beta, A1, A2, r, r / bound, flag))

print("\nmax (A2/A1)/3n: %.4f  all<=3n: %s" % (max(ratios), all(c <= 1.0 + 1e-6 for c in ratios)))
