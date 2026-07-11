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

def conv_form_two(u, m, c):
    # claimed: sum over a != 0, (c-a) != 0  of u[a]*u[(c-a)%m]
    total = 0+0j
    for a in range(m):
        ca = (c - a) % m
        if a != 0 and ca != 0:
            total += u[a]*u[ca]
    return total

random.seed(1)
for m in [3, 5, 7, 9, 15]:
    u = [cmath.exp(2j*cmath.pi*random.random()) for _ in range(m)]
    ok = True
    for c in range(m):
        a = phaseSum(u, m, 2, c)
        b = conv_form_two(u, m, c)
        if abs(a-b) > 1e-9:
            ok = False
            print("MISMATCH", m, c, a, b)
    T2 = sum(abs(phaseSum(u, m, 2, c))**2 for c in range(m))
    # all-ones case: phaseSum 1 2 c counts pairs (a, c-a) with a!=0 and c-a!=0
    uo = [1+0j]*m
    bad = []
    for c in range(m):
        cval = round(phaseSum(uo, m, 2, c).real)
        pred = (m-1) if c == 0 else (m-2)
        if cval != pred:
            bad.append((c, cval, pred))
    print(f"m={m} convPASS={ok} T2={T2:.4f} allones_floor_bad={bad}")
