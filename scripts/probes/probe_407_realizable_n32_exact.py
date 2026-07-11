#!/usr/bin/env python3
"""
import math
probe_407_realizable_n32_exact.py  (#407)

Exact-integer verification of the n=32 realizable-BHBI break witnesses from
probe_407_realizable_bhbi_verify.py (V5). Confirm, with NO modular shortcut ambiguity,
that the reported g in {-2..2}^16 genuinely satisfies sum_j g_j omega^j == 0 mod p, with
omega a primitive 32nd root (omega^16 == -1), proper subgroup, prize prime p~32^4.

Also: re-derive omega independently and recompute the FULL sum as an exact integer
(no running mod) then reduce, to rule out a modular-arithmetic artifact.
"""
import math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_2pow_root(p, m):
    n = 1 << m
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    for base in range(2, p):
        r = pow(base, e, p)
        if pow(r, n // 2, p) != 1 and pow(r, n, p) == 1:
            return r
    return None

CASES = [
    (32801, [-2,-1,2,-1,1,0,2,2,-2,-2,-2,-2,-2,-2,-2,-2]),
    (1048609, [-1,-1,0,2,1,1,-1,2,-2,-2,-2,-2,-2,-2,-2,-2]),
    (33554593, [1,0,0,-1,0,-1,-2,-1,-2,-2,-2,-2,-1,-2,1,-1]),
]

def main():
    m = 5; n = 32; N = 16
    for p, g in CASES:
        assert isprime(p), p
        om = primitive_2pow_root(p, m)
        # omega^16 == -1 (proper: primitive 32nd root, so the subgroup mu_32 is THIN in F_p*)
        half = pow(om, N, p)
        # exact integer sum, then reduce
        S = 0
        for j in range(N):
            S += g[j] * pow(om, j, p)
        Smod = S % p
        maxabs = max(abs(x) for x in g)
        nonzero = any(x != 0 for x in g)
        beta = math.log(p, 32)
        print("p=%10d beta=%.3f omega=%d omega^16==-1:%s  max|g|=%d nonzero:%s  sum mod p=%d  S=%d  -> %s" % (
            p, beta, om, half==p-1, maxabs, nonzero, Smod, S,
            "VALID realizable relation (chain BHBI(omega,16,2) FALSE)" if (Smod==0 and nonzero and maxabs<=2) else "INVALID"))

if __name__ == "__main__":
    main()
