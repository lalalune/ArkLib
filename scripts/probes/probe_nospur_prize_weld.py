# Probe: in the no-spurious regime (girth > 2r, i.e. p large vs cyclotomic norms),
# does char-p additive energy E_r(mu_n) EXACTLY equal char-0 zeroSumCount, and does
# the resulting per-frequency sup obey the prize sqrt-shape M^2 <= 2e*n*r?
# PROPER thin mu_n only (n=2^a, p=1 mod n, (p-1)/n>=2, NEVER n=q-1). Multi-prime incl p>>n^3 + Fermat.
import cmath, math, itertools

def primitive_root(p):
    def order(g):
        x = 1
        for k in range(1, p):
            x = (x * g) % p
            if x == 1:
                return k
        return None
    for g in range(2, p):
        if order(g) == p - 1:
            return g
    return None

def char0_zeroSumCount(n, twor):
    # char-0 additive energy of mu_n in C: #{(z_1..z_{2r}) in mu_n^{2r}: sum=0}
    roots = [cmath.exp(2j * math.pi * k / n) for k in range(n)]
    cnt = 0
    for tup in itertools.product(range(n), repeat=twor):
        s = sum(roots[k] for k in tup)
        if abs(s) < 1e-7:
            cnt += 1
    return cnt

def charp_energy(p, n, twor):
    # mu_n subgroup of F_p^*, additive energy = #{(z_1..z_{2r}): sum=0 in F_p}
    g = primitive_root(p)
    step = (p - 1) // n
    H = [pow(g, (step * k) % (p - 1), p) for k in range(n)]
    cnt = 0
    for tup in itertools.product(range(n), repeat=twor):
        s = sum(H[k] for k in tup) % p
        if s == 0:
            cnt += 1
    return cnt

def doublefact(m):
    r = 1
    k = m
    while k > 0:
        r *= k
        k -= 2
    return r

print(f"{'n':>3} {'p':>7} {'r':>2} {'E_char0':>9} {'E_charp':>9} {'spur=0?':>8} {'Wick':>10} {'E<=Wick?':>9}")
cases = [
    (4, 17, 1), (4, 17, 2), (4, 41, 1), (4, 41, 2),
    (8, 17, 1), (8, 17, 2), (8, 97, 1), (8, 97, 2),
    (8, 257, 1), (8, 257, 2),      # Fermat
    (4, 4129, 2), (8, 4129, 2),    # p >> n^3
]
passes = 0
total = 0
for (n, p, r) in cases:
    if (p - 1) % n != 0:
        continue
    if (p - 1) // n < 2:
        continue
    twor = 2 * r
    e0 = char0_zeroSumCount(n, twor)
    ep = charp_energy(p, n, twor)
    wick = doublefact(2 * r - 1) * (n ** r)
    nospur = (ep == e0)
    eok = (ep <= wick)
    total += 1
    if nospur and eok:
        passes += 1
    print(f"{n:>3} {p:>7} {r:>2} {e0:>9} {ep:>9} {str(nospur):>8} {wick:>10} {str(eok):>9}")
print(f"\nPASS {passes}/{total}  (no-spur AND E_charp<=Wick)")
