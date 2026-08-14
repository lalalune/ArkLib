import sympy as sp

def mu_n_field(p, n):
    assert (p - 1) % n == 0
    g = sp.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return sorted({pow(h, k, p) for k in range(n)})

def repcount_direct(S, c, p):
    Sset = set(S)
    return sum(1 for y in S if (c - y) % p in Sset)

def gcd_deg_mod_p(p, n, c):
    X = sp.symbols('X')
    f = sp.Poly(X**n - 1, X, modulus=p)
    gp = sp.Poly((c - X)**n - 1, X, modulus=p)
    g = f.gcd(gp)
    return g.degree()

cases = [(257, 16), (257, 8), (193, 16), (641, 16), (769, 16), (12289, 16), (12289, 32)]
for p, n in cases:
    if (p - 1) % n:
        continue
    S = mu_n_field(p, n)
    cs = [S[1], S[2], (S[1] + S[3]) % p, (3 * S[2]) % p, (S[5] + 7) % p]
    print("p=%d n=%d |mu_n|=%d" % (p, n, len(S)))
    for c in cs:
        if c == 0:
            continue
        rc = repcount_direct(S, c, p)
        dg = gcd_deg_mod_p(p, n, c)
        print("   c=%6d  repCount=%3d  deg_gcd=%3d  match=%s" % (c, rc, dg, rc == dg))
