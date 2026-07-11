"""Independent verification of THE KEY REDUCTION before trusting it (derived by
hand from DERIVED-672.md, validated here against raw polynomial arithmetic).

Claim: e = Prod_{c in B}(X^2 - z_c) * Prod_i(X - x_i) * (X - xi), xi = -Sum x_i,
x_i = zeta^{o_i + s*d_i}, z_c = zeta^{2c}, is monic deg s+2 with coeff(X^{s+1})=0
and  coeff(X^s) = LAM - alpha,  where
  alpha = e2(x) + e1(O_z) + e1(B_z) - z*      (the 2-power multiset sum)
        = [Sum_{i<j} x_i x_j] + [Sum_i zeta^{2 o_i}] + [Sum_{c in B} zeta^{2c}] + LAM
(LAM = -z*, z* = zeta^{s/2}).  Hence membership in the marginal layer
(coeff(X^s) == LAM, i.e. w - e is a deg<s codeword) is EXACTLY the linear
equation  Sum_{c in B} G[c] == ZS - fixed,  fixed = e2(x) + e1(O_z)  -- the
fixed_part / w_fiber / target used by the falsifier.  Checked at all
(prime, scale) production pairs + small primes, r in {3,5}, random configs.
"""
import random

def gen(p):
    f, m = [], p - 1
    d, t = 2, m
    while d * d <= t:
        if t % d == 0:
            f.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        f.append(t)
    for g in range(2, 1000):
        if all(pow(g, m // q, p) != 1 for q in f):
            return g
    raise RuntimeError

def polymul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return r

BB = 15 * (1 << 27) + 1          # BabyBear
P2 = 3 * (1 << 30) + 1           # second production prime
CASES = [(BB, 32), (BB, 64), (P2, 32), (P2, 64), (97, 32), (193, 64)]
random.seed(20260610)

for P, n in CASES:
    s = n // 2
    g0 = 31 if P == BB else gen(P)
    assert (P - 1) % n == 0
    h = pow(g0, (P - 1) // n, P)
    H = [pow(h, i, P) for i in range(n)]
    assert len(set(H)) == n and H[s] == P - 1   # h has exact order n
    G = [H[(2 * c) % n] for c in range(s)]
    ZS = H[s // 2]
    assert pow(ZS, 2, P) == P - 1               # 4th root of unity
    LAM = (P - ZS) % P
    nzero = 0
    for trial in range(120):
        r = random.choice([3, 5])
        b = (s + 1 - r) // 2
        O = sorted(random.sample(range(s), r))
        m = random.randrange(1 << (r - 1))
        d = [0] + [(m >> (i - 1)) & 1 for i in range(1, r)]
        B = random.sample([c for c in range(s) if c not in O], b)
        x = [H[O[i] + s * d[i]] for i in range(r)]
        xi = (P - sum(x) % P) % P
        # ground truth: full polynomial product mod p
        e = [1]
        for c in B:
            e = polymul(e, [(P - G[c]) % P, 0, 1], P)
        for rt in x + [xi]:
            e = polymul(e, [(P - rt) % P, 1], P)
        assert len(e) == s + 3 and e[s + 2] == 1
        assert e[s + 1] == 0, "coeff X^{s+1} not 0: xi convention broken"
        # the reduction
        e2x = sum(x[i] * x[j] for i in range(r) for j in range(i + 1, r)) % P
        e1Oz = sum(G[o] for o in O) % P
        sB = sum(G[c] for c in B) % P
        alpha = (e2x + e1Oz + sB + LAM) % P
        assert e[s] == (LAM - alpha) % P, \
            f"REDUCTION WRONG at p={P} n={n}: e[s]={e[s]} lam-a={(LAM-alpha)%P}"
        # membership predicate == linear equation in the B-subset sum
        target = (ZS - (e2x + e1Oz)) % P
        assert (e[s] == LAM) == (sB == target)
        nzero += (e[s] == LAM)
    print(f"p={P:>10} n={n:>2} g0={g0:>2}: 120/120 random (r,O,m,B) configs: "
          f"e[s] == LAM - alpha EXACTLY; predicate==linear-eq; "
          f"{nzero} random hits")
print("REDUCTION VERIFIED: fixed = e2(x)+e1(O_z), w_fiber = z_c = H[2c], "
      "target = ZS - fixed; all signs pinned by raw polynomial arithmetic")
