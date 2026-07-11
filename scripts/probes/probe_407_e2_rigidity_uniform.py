import itertools, cmath, sympy, random

def e2_complex(U, k):
    z = cmath.exp(2j*cmath.pi/(2**k))
    pts = [z**i for i in U]
    e1 = sum(pts); p2 = sum(x*x for x in pts)
    return (e1*e1 - p2)/2

def e2_modp(U, g, p):
    pts = [pow(g, i, p) for i in U]
    e1 = sum(pts) % p
    p2 = sum((x*x) % p for x in pts) % p
    inv2 = pow(2, p-2, p)
    return ((e1*e1 - p2) * inv2) % p

def primitive_2k_root(p, k):
    order = 2**k
    if (p-1) % order != 0: return None
    h = (p-1)//order
    for _ in range(300):
        a = random.randrange(2, p-1)
        g = pow(a, h, p)
        if pow(g, order, p) == 1 and pow(g, order//2, p) != 1:
            return g
    return None

random.seed(7)
fails = 0; checks = 0; per_u_above = 0
for k in [2,3,4]:
    nn = 2**k
    # primes p == 1 mod 2^k, take several large ones (well above per-U thresholds for small |U|)
    plist = []
    pp = nn
    while len(plist) < 5:
        pp += 1
        if sympy.isprime(pp) and (pp-1) % nn == 0:
            plist.append(pp)
    # also add some genuinely large thin primes
    big = sympy.nextprime(10**6)
    while len(plist) < 8:
        if (big-1) % nn == 0: plist.append(big)
        big = sympy.nextprime(big)
    for p in plist:
        g = primitive_2k_root(p, k)
        if g is None: continue
        for r in range(2, nn+1):
            thr = (r*r + r)**(2**(k-1))
            for U in itertools.combinations(range(nn), r):
                c0 = abs(e2_complex(U,k)) < 1e-9
                cp = (e2_modp(U,g,p) == 0)
                checks += 1
                if p > thr:
                    per_u_above += 1
                    if c0 != cp:
                        fails += 1
                        print(f"FAIL k={k} p={p} U={U} char0={c0} modp={cp} thr={thr}")
print(f"checks={checks} per_u_above_threshold={per_u_above} fails={fails}")
