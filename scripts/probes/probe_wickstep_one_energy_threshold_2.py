import cmath, math

def order(a, p):
    o = 1
    cur = a % p
    while cur != 1:
        cur = (cur * a) % p
        o += 1
    return o

def gen_of(p):
    for a in range(2, p):
        if order(a, p) == p - 1:
            return a
    return None

def subgroup(p, n, gen):
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

def moments(p, n, gen):
    sub = subgroup(p, n, gen)
    A1 = 0.0
    A2 = 0.0
    A3 = 0.0
    for b in range(1, p):
        m = eta_abs2(b, p, sub)
        A1 += m
        A2 += m * m
        A3 += m * m * m
    return A1 / p, A2 / p, A3 / p

# WickStepCross r: A_{r+1}*Wick_r <= A_r*Wick_{r+1}
# Wick_r = (2r-1)!! |G|^r. ratio Wick_{r+1}/Wick_r = (2r+1)|G|.
# step r=1: A_2/A_1 <= 3|G|.  step r=2: A_3/A_2 <= 5|G|.
# THICK control (n=q-1 forbidden by rule 2); use PROPER subgroups + also test
# a THICK-ish case to confirm thinness-essential.

print("== prize-regime PROPER subgroups: check A2/A1 <= 3n and A3/A2 <= 5n ==")
pairs = [(7681,8),(7681,16),(7681,32),(12289,16),(12289,32),
         (40961,16),(40961,32),(40961,64),(786433,16),(786433,32),(786433,64),(786433,128)]
ok = True
for p, n in pairs:
    if (p - 1) % n != 0:
        print("SKIP", p, n); continue
    g = gen_of(p)
    A1, A2, A3 = moments(p, n, g)
    r1 = A2 / A1
    r2 = A3 / A2
    beta = math.log(p) / math.log(n)
    f1 = "OK" if r1 <= 3 * n + 1e-6 else "VIOL"
    f2 = "OK" if r2 <= 5 * n + 1e-6 else "VIOL"
    if r1 > 3*n+1e-6 or r2 > 5*n+1e-6: ok = False
    print("p=%7d n=%3d b=%.2f  A2/A1=%8.3f /3n=%.4f %s   A3/A2=%9.3f /5n=%.4f %s"
          % (p, n, beta, r1, r1/(3*n), f1, r2, r2/(5*n), f2))

print("\nall prize-regime steps hold:", ok)

# THICK comparison: large subgroup index 2 (n=(p-1)/2) -> NOT prize, just to see if step is thickness-monotone
print("\n== thick check (n=(p-1)/2, index 2 -- near-full, to test thinness-essentiality of the SLACK) ==")
for p in [193, 257, 769]:
    n = (p - 1) // 2
    g = gen_of(p)
    A1, A2, A3 = moments(p, n, g)
    r1 = A2 / A1
    print("p=%5d n=%4d (index2)  A2/A1=%.3f  3n=%d  ratio=%.4f" % (p, n, r1, 3*n, r1/(3*n)))
