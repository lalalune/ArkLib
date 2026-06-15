#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : M at HUGE prize-scale primes p ~ n*2^128, WITHOUT full factorization.

Build mu_n directly: pick random a, h = a^{(p-1)/n} mod p; if h has order exactly n it generates mu_n.
(No primitive root / no factoring p-1 needed.)  Then M = #{u in mu_n : (1+u) in mu_n}.
This reaches the genuine prize regime p ~ n*2^128.
"""
import random
from sympy import isprime, nextprime

def find_mu_n_gen(n, p):
    """Return an element of order exactly n in F_p^* (assumes n | p-1)."""
    e = (p-1)//n
    for _ in range(200):
        a = random.randrange(2, p-1)
        h = pow(a, e, p)
        if h == 1:
            continue
        # check order is exactly n: h^n=1 (auto) and h^(n/q)!=1 for primes q|n. n=2^k so only q=2.
        if pow(h, n//2, p) != 1:
            return h
    return None

def mu_n_set(n, p):
    h = find_mu_n_gen(n, p)
    if h is None:
        return None
    s = set(); cur = 1
    for _ in range(n):
        s.add(cur); cur = cur*h % p
    return s

def bgk_M(n, p):
    G = mu_n_set(n, p)
    if G is None:
        return None
    return sum(1 for u in G if (1+u) % p in G)

def prime_with_div(n, kbits, tries=300000):
    """A prime p ~ n*2^kbits with n | p-1: p = 1 + n*m, m near 2^kbits."""
    m0 = 1 << kbits
    for dm in range(tries):
        for m in (m0+dm, m0-dm):
            if m <= 0: continue
            p = 1 + n*m
            if isprime(p):
                return p
    return None

def main():
    random.seed(12345)
    print("M at HUGE primes p ~ n*2^k (prize regime k=128), density = n/(p-1) ~ 2^-k.\n")
    print(f"{'n':>5} {'k':>4} {'density':>11} {'M':>4}   p")
    print("-"*70)
    for n in [16,32,64,128,256,1024]:
        for k in [64,96,128]:
            p = prime_with_div(n, k)
            if p is None:
                print(f"{n:>5} {k:>4}  no prime"); continue
            M = bgk_M(n, p)
            dens = n/(p-1)
            print(f"{n:>5} {k:>4} {dens:>11.3e} {str(M):>4}   {p}")
    print("\nVERDICT CHECK: in the prize regime (k=128, density ~ 2^-128) is M = 0?")

if __name__=="__main__":
    main()
