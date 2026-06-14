"""
L1 / #407 part (2): FAST genuine-bad-prime growth via meet-in-the-middle.

A genuine bad prime p (== 1 mod n) admits an antipodal-free U subset mu_n with
sum_{u in U} u == 0 AND sum_{u in U} u^3 == 0 (mod p).  We detect the SMALLEST such config
(size 4, then 6) by MITM: split U = A cup B (|A|=|B|), require
   sum_A (u, u^3) == - sum_B (u, u^3)   in (F_p)^2.
Hash all half-sums of A, look up the negation among B-halves, enforce antipodal-free + disjoint.

This is fast enough to push n=64, 128, 256 and FIT the growth law of the max genuine bad prime.
"""
import itertools
from collections import defaultdict
from sympy import primerange
from math import log


def primitive_root_mod(p, n):
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    HALF = n // 2
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, HALF, p) == p - 1:
            return g
    return None


def has_genuine_size6(n, p, g):
    """Antipodal-free 6-subset of exponents with sum g^j=0 and sum g^{3j}=0 (mod p), via 3+3 MITM."""
    HALF = n // 2
    pw = [pow(g, j, p) for j in range(n)]
    pw3 = [pow(g, (3 * j) % n, p) for j in range(n)]
    triplesum = defaultdict(list)
    rng = range(n)
    for tri in itertools.combinations(rng, 3):
        # antipodal-free within the triple (cheap prune)
        i, j, k = tri
        if (i + HALF) % n in (j, k) or (j + HALF) % n == k:
            continue
        key = (sum(pw[t] for t in tri) % p, sum(pw3[t] for t in tri) % p)
        triplesum[key].append(tri)
    for key, lst in triplesum.items():
        negkey = ((-key[0]) % p, (-key[1]) % p)
        if negkey in triplesum:
            for t1 in lst:
                s1 = set(t1)
                for t2 in triplesum[negkey]:
                    S = s1 | set(t2)
                    if len(S) != 6:
                        continue
                    if any(((x + HALF) % n) in S for x in S):
                        continue
                    return True
    return False


def max_genuine_bad_size6(n, hi):
    bad = []
    for p in primerange(n + 1, hi):
        if p % n != 1:
            continue
        g = primitive_root_mod(p, n)
        if g is None:
            continue
        if has_genuine_size6(n, p, g):
            bad.append(p)
    return bad


if __name__ == "__main__":
    print("FAST genuine-bad-prime (size-6 MITM, the minimal spurious size) growth law:\n")
    rows = []
    for n, hi in [(16, 60000), (32, 40000), (64, 60000), (128, 120000)]:
        bad = max_genuine_bad_size6(n, hi)
        mx = max(bad) if bad else 0
        rows.append((n, mx, len(bad)))
        if bad:
            print(f"n={n:4d}: size-6 genuine bad primes (<{hi}): {bad[:10]}"
                  f"{'...' if len(bad)>10 else ''}; count={len(bad)} MAX={mx} "
                  f"log_n(max)={log(mx)/log(n):.3f} max/n^2={mx/n**2:.2f}")
        else:
            print(f"n={n:4d}: NO size-6 genuine bad prime < {hi}")
    print()
    print("growth-law fit:  log_n(max_bad) across n (size-4 minimal configs)")
    for n, mx, c in rows:
        if mx > 0:
            print(f"   n={n:4d}  max={mx:7d}  log_n(max)={log(mx)/log(n):.3f}  log2(max)/mu={log(mx)/log(2)/(n.bit_length()-1):.3f}")
