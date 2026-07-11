"""Fast full-F_p* sweep: r(c) = deg gcd(X^n-1, (1+X)^n - c^n), thin 2-power mu_n,
p>>n^3, p==1 mod n. Pure-int poly gcd over F_p (no sympy per-c). Find MAX r(c)
(the M-relevant worst case) and confirm match + sharpness (deg gcd < n) everywhere.
NEVER n=q-1."""


def poly_mod(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_rem(a, b, p):
    # remainder of a mod b over F_p, lists low->high degree
    a = poly_mod(a[:], p)
    b = poly_mod(b[:], p)
    db = len(b) - 1
    inv_lead = pow(b[-1], p - 2, p)
    while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
        da = len(a) - 1
        if da < db:
            break
        coef = (a[-1] * inv_lead) % p
        shift = da - db
        for i in range(len(b)):
            a[i + shift] = (a[i + shift] - coef * b[i]) % p
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return poly_mod(a, p)


def poly_gcd_deg(a, b, p):
    a = poly_mod(a[:], p)
    b = poly_mod(b[:], p)
    while not (len(b) == 1 and b[0] == 0):
        a, b = b, poly_rem(a, b, p)
    return len(a) - 1  # degree of gcd (monic-irrelevant for degree)


def binom_row(n, p):
    # coefficients of (1+X)^n mod p, low->high
    row = [0] * (n + 1)
    row[0] = 1
    for k in range(1, n + 1):
        row[k] = row[k - 1] * (n - k + 1) % p * pow(k, p - 2, p) % p
    return row


def primitive_root(p):
    # small p only
    from sympy import primitive_root as pr
    return pr(p)


primes_n = [(7681, 8), (8161, 8), (12289, 16), (40961, 16)]
for (p, n) in primes_n:
    assert (p - 1) % n == 0 and p > n**3
    g = primitive_root(p)
    base = pow(g, (p - 1) // n, p)
    mu = [pow(base, k, p) for k in range(n)]
    onepw = binom_row(n, p)  # (1+X)^n coeffs
    xn1 = [(-1) % p] + [0] * (n - 1) + [1]  # X^n - 1
    maxr = -1
    maxc = None
    allsharp = True
    allmatch = True
    for c in range(1, p):
        cn = pow(c, n, p)
        # r(c): brute over mu_n
        r = sum(1 for w in mu if pow((1 + w) % p, n, p) == cn)
        # deg gcd(X^n-1, (1+X)^n - c^n)
        g2 = onepw[:]
        g2[0] = (g2[0] - cn) % p
        dg = poly_gcd_deg(xn1, g2, p)
        if r != dg:
            allmatch = False
        if dg >= n:
            allsharp = False
        if r > maxr:
            maxr = r
            maxc = c
    print("p=%d n=%d : max r(c)=%d at c=%d ; full-sweep match=%s all-sharp(deg<n)=%s"
          % (p, n, maxr, maxc, allmatch, allsharp))
