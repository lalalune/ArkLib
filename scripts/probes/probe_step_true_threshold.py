"""TRUE Sidon threshold for mu_n (n=2^a) over F_p, c != 0:
the in-tree bound is p > 12^(n/4) (EXPONENTIAL). Empirically the largest bad prime is tiny.
Find the largest prime p with a genuine c!=0 parallelogram (repCount>=3 ordered at some c!=0),
scanning ALL p = 1 mod n up to a large bound. Compare to n^2, n^3, 12^(n/4).
"""
import sympy


def order_subgroup(p, n):
    g = 2
    while True:
        x = 1
        isg = True
        for _ in range(p - 2):
            x = (x * g) % p
            if x == 1:
                isg = False
                break
        if isg:
            break
        g += 1
    h = pow(g, (p - 1) // n, p)
    return sorted(set(pow(h, j, p) for j in range(n)))


def maxrep_nonzero(p, n):
    mu = order_subgroup(p, n)
    from collections import Counter
    r = Counter()
    for g1 in mu:
        for g2 in mu:
            c = (g1 + g2) % p
            if c != 0:
                r[c] += 1
    return max(r.values()) if r else 0


for n in (4, 8, 16, 32):
    largest_bad = None
    bound = max(50000, 20 * n * n)
    p = 3
    while p < bound:
        if (p - 1) % n == 0 and (p - 1) != n and sympy.isprime(p):
            if maxrep_nonzero(p, n) >= 3:
                largest_bad = p
        p += 1
    import math
    bound_intree = 12 ** (n / 4)
    print(f"n={n:2d}: largest bad prime (c!=0 parallelogram) below {bound} = {largest_bad}; "
          f"n^2={n*n}, n^3={n**3}, 12^(n/4)={bound_intree:.3g}")
