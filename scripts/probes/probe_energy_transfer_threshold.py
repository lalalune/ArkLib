import numpy as np
from sympy import isprime

def find_ntt_prime(a, target):
    """smallest prime p >= target with p == 1 mod 2^a."""
    m = 1 << a
    p = target + ((1 - target) % m)
    if p < target: p += m
    while not isprime(p): p += m
    return p

def order_2a_root(p, a):
    """a primitive 2^a-th root of unity mod p (p == 1 mod 2^a)."""
    m = 1 << a
    e = (p - 1) // m
    import random
    random.seed(12345 + p % 1000)
    for _ in range(200):
        g = pow(random.randrange(2, p-1), e, p)
        # g has order dividing m; check order exactly m (g^{m/2} != 1)
        if pow(g, m // 2, p) != 1:
            return g
    raise RuntimeError("no root")

def subgroup(p, a):
    g = order_2a_root(p, a)
    s = []
    x = 1
    for _ in range(1 << a):
        s.append(x); x = (x * g) % p
    assert len(set(s)) == (1 << a), "not full subgroup"
    return s

def energy_and_charsum(p, a):
    n = 1 << a
    ind = np.zeros(p, dtype=np.float64)
    for x in subgroup(p, a): ind[x] = 1.0
    F = np.fft.rfft(ind)            # eta_b for b = 0..p//2 ; use full for max
    Ff = np.fft.fft(ind)
    mag = np.abs(Ff)
    # B = max over b != 0 of |eta_b|
    B = float(np.max(mag[1:]))
    # E = (1/p) sum_b |eta_b|^4   (additive energy of the subgroup)
    E = float(np.sum(mag**4) / p)
    return n, E, B

print(f"{'a':>2} {'n':>6} {'p':>12} {'p/n^5':>8} {'E':>12} {'E/(3n^2-3n)':>12} {'E/n^2.45':>10} {'B':>10} {'B/sqrt(n)':>10}")
# Fixed-n threshold sweep (n=16): vary p from tiny to ~n^5 and beyond
for a in [3,4,5,6]:
    n = 1 << a
    n5 = n**5
    targets = [n*n, n**3, n**4, n5, n5*64]  # p across the suspected threshold
    for t in targets:
        if t < n*2: continue
        try:
            p = find_ntt_prime(a, max(t, n*2+1))
            if p > 8_000_000: continue   # FFT size cap
            nn, E, B = energy_and_charsum(p, a)
            base = 3*n*n - 3*n
            print(f"{a:>2} {n:>6} {p:>12} {p/n5:>8.2f} {E:>12.1f} {E/base:>12.4f} {E/(n**2.45):>10.3f} {B:>10.2f} {B/np.sqrt(n):>10.3f}")
        except Exception as ex:
            print(f"a={a} p~{t}: {ex}")
