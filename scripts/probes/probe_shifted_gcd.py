import sympy as sp

def mu_n_field(p, n):
    assert (p - 1) % n == 0
    g = sp.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return sorted({pow(h, k, p) for k in range(n)})

def repcount_direct(S, c, p):
    Sset = set(S)
    return sum(1 for y in S if (c - y) % p in Sset)

def fiber_count(S, c, p, n):
    Sset = set(S)
    cn = pow(c, n, p)
    return sum(1 for w in S if pow((1 + w) % p, n, p) == cn)

def gcd_deg(p, n, c):
    X = sp.symbols('X')
    f = sp.Poly(X**n - 1, X, modulus=p)
    g = sp.Poly((1 + X)**n - pow(c, n, p), X, modulus=p)
    return f.gcd(g).degree()

def roots_of_gcd_count(p, n, c):
    X = sp.symbols('X')
    f = sp.Poly(X**n - 1, X, modulus=p)
    g = sp.Poly((1 + X)**n - pow(c, n, p), X, modulus=p)
    d = f.gcd(g)
    # count distinct roots in F_p
    cnt = 0
    for x in range(p):
        if d.eval(x) % p == 0:
            cnt += 1
    return cnt

cases = [(257, 16), (257, 8), (193, 16), (641, 16), (12289, 16), (12289, 32)]
for p, n in cases:
    if (p - 1) % n:
        continue
    S = mu_n_field(p, n)
    cs = [S[1], S[2], (S[1] + S[3]) % p, (3 * S[2]) % p, (S[4] + 5) % p]
    print("p=%d n=%d" % (p, n))
    for c in cs:
        if c == 0:
            continue
        rc = repcount_direct(S, c, p)
        fc = fiber_count(S, c, p, n)
        dg = gcd_deg(p, n, c)
        rg = roots_of_gcd_count(p, n, c)
        ok = (rc == fc == dg == rg)
        print("  c=%6d rep=%2d fiber=%2d degGcd=%2d rootsGcd=%2d all_eq=%s rc_le_deg=%s"
              % (c, rc, fc, dg, rg, ok, rc <= dg))
