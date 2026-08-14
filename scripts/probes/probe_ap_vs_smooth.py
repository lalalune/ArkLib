#!/usr/bin/env python3
"""#389 AP vs SMOOTH supply (= max e-symm fiber over t-subsets). Robust version.
Confirms: additively-structured (AP) domain -> superlinear (subset-sum concentration);
multiplicative subgroup (smooth) -> ~linear (additive non-concentration of mu_n).
This is the elementary shadow of BCIS-2025 Thm 1.6 (a jumps O(n)->Omega(n^2) at Johnson)."""
import itertools, random
from math import comb
from collections import defaultdict

def is_prime(p):
    if p < 2: return False
    if p % 2 == 0: return p == 2
    i = 3
    while i*i <= p:
        if p % i == 0: return False
        i += 2
    return True

def prime_with_divisor(nmin_q, n):
    """smallest prime q >= nmin_q with n | q-1."""
    q = nmin_q + ((1 - nmin_q) % n)  # q ≡ 1 mod n
    while True:
        if q >= nmin_q and is_prime(q): return q
        q += n

def prime_factors(n):
    f = set(); d = 2
    while d*d <= n:
        while n % d == 0: f.add(d); n//=d
        d += 1
    if n > 1: f.add(n)
    return f

def subgroup_mu_n(q, n):
    """the n-th roots of unity in F_q (n | q-1)."""
    assert (q-1) % n == 0
    for a in range(2, q):
        h = pow(a, (q-1)//n, q)
        if all(pow(h, n//p, q) != 1 for p in prime_factors(n)):
            return sorted({pow(h, i, q) for i in range(n)})
    return None

def esymm(A, q, upto):
    e = [1] + [0]*upto
    for a in A:
        for i in range(min(len(e)-1, upto), 0, -1):
            e[i] = (e[i] + a*e[i-1]) % q
    return tuple(e[1:upto+1])

def max_fiber(dom, q, t, ns):
    fib = defaultdict(int)
    for A in itertools.combinations(dom, t):
        fib[esymm(A, q, ns)] += 1
    return max(fib.values())

def run():
    rng = random.Random(3)
    print("=== m=0 (t=k+1=3): max e1-fiber (subset-sum), AP vs SMOOTH vs RANDOM, q~4000>>n ===")
    print(f"{'n':>4} {'AP':>6} {'smooth':>7} {'rand':>6}   (n^2/12={'':>0})")
    for n in [10, 12, 14, 16, 18, 20, 24, 28, 32]:
        t = 3
        q = prime_with_divisor(4000, n)
        domAP = list(range(n))
        mAP = max_fiber(domAP, q, t, 1)
        sd = subgroup_mu_n(q, n)
        mS = max_fiber(sd, q, t, 1) if sd else -1
        domR = sorted(rng.sample(range(q), n))
        mR = max_fiber(domR, q, t, 1)
        print(f"{n:>4} {mAP:>6} {mS:>7} {mR:>6}   ({n*n/12:.1f})")

    print("\n=== m=1 (t=4): max (e1,e2)-fiber, AP vs SMOOTH vs RANDOM, q~4000>>n ===")
    print(f"{'n':>4} {'AP':>6} {'smooth':>7} {'rand':>6}   (n)")
    for n in [10, 12, 14, 16, 18, 20, 24, 28]:
        t = 4
        q = prime_with_divisor(4000, n)
        domAP = list(range(n))
        mAP = max_fiber(domAP, q, t, 2)
        sd = subgroup_mu_n(q, n)
        mS = max_fiber(sd, q, t, 2) if sd else -1
        domR = sorted(rng.sample(range(q), n))
        mR = max_fiber(domR, q, t, 2)
        print(f"{n:>4} {mAP:>6} {mS:>7} {mR:>6}   ({n})")

    print("\n=== m=2 (t=5): max (e1,e2,e3)-fiber, AP vs SMOOTH, q~4000>>n ===")
    print(f"{'n':>4} {'AP':>6} {'smooth':>7}")
    for n in [12, 16, 20, 24, 28]:
        t = 5
        q = prime_with_divisor(4000, n)
        domAP = list(range(n))
        mAP = max_fiber(domAP, q, t, 3)
        sd = subgroup_mu_n(q, n)
        mS = max_fiber(sd, q, t, 3) if sd else -1
        print(f"{n:>4} {mAP:>6} {mS:>7}")

if __name__ == "__main__":
    run()
