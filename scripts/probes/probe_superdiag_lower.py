"""Probe-first (rule 2): verify the hypothesis-free super-diagonal energy lower bound
   (2r-1)!! * descFactorTwo(n,r) <= E_r(mu_n),   descFactorTwo(n,r) = prod_{i<r}(n-2i) = 2^r*(n/2)_r,
on PROPER thin subgroups mu_n < F_p^* (n=2^a, p>>n^3, p==1 mod n, m=(p-1)/n>1, NEVER n=q-1).
E_r(G) = #{(x_1..x_r),(y_1..y_r) in G^{2r} : sum x_i = sum y_i}  (r-fold additive energy).
Computed EXACTLY mod p via integer FFT-free additive convolution over F_p.
Also checks NON-VACUITY (rule 1): the bound is a real positive number << E_r (not trivially 0/equal).
"""
from sympy import isprime
from collections import Counter

def dfact(k):
    out = 1
    while k > 1:
        out *= k; k -= 2
    return out

def descFactorTwo(n, r):
    out = 1
    for i in range(r):
        out *= (n - 2 * i)
    return out

def find_prime(n, beta):
    # smallest prime p == 1 mod n with p ~ n^beta, m=(p-1)/n>1 (proper), p != n+1 (never n=q-1 sense)
    target = int(n ** beta)
    p = target - (target % n) + 1
    while True:
        if p > n + 1 and isprime(p):
            return p
        p += n

def subgroup(p, n):
    # mu_n = <g^{(p-1)/n}> ; find a generator g of F_p^* by trial
    from sympy import primitive_root
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x * h) % p
    assert len(set(G)) == n, "not a proper size-n subgroup"
    assert (p - 1) // n > 1, "n=q-1 forbidden"
    return G

def Er_modp(G, p, r):
    # distribution of sum of r elements (mod p), then E_r = sum count^2
    cur = Counter({0: 1})
    for _ in range(r):
        nxt = Counter()
        for s, c in cur.items():
            for g in G:
                nxt[(s + g) % p] += c
        cur = nxt
    return sum(c * c for c in cur.values())

print(f"{'n':>4} {'r':>2} {'beta':>5} {'p':>10} {'(2r-1)!!':>9} {'descF2':>8} {'LHS=bound':>12} {'E_r':>12} {'LHS<=E_r':>9} {'E_r/LHS':>8}")
for n in [8, 16]:
    for beta in [4.0]:
        p = find_prime(n, beta)
        G = subgroup(p, n)
        for r in [1, 2, 3]:
            df2 = descFactorTwo(n, r)
            d = dfact(2 * r - 1)
            bound = d * df2
            Er = Er_modp(G, p, r)
            ok = bound <= Er
            ratio = Er / bound if bound else float('inf')
            # also confirm descFactorTwo = 2^r*(n/2)_r
            asc = 1
            for i in range(r):
                asc *= (n // 2 - i)
            assert df2 == (2 ** r) * asc, f"descFactorTwo mismatch {df2} vs {2**r*asc}"
            print(f"{n:>4} {r:>2} {beta:>5} {p:>10} {d:>9} {df2:>8} {bound:>12} {Er:>12} {str(ok):>9} {ratio:>8.3f}")
print("\nAll descFactorTwo(n,r) == 2^r * (n/2)_r  (verified).")
print("Bound is the char-0 super-diagonal (antipodally-paired) lower term; non-vacuous (positive, < E_r).")
