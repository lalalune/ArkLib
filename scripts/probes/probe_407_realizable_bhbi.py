#!/usr/bin/env python3
"""
probe_407_realizable_bhbi.py  (#407)

DECISIVE deconfliction of the 032525 "C*(n=16,prize)=4 breaks the chain" refutation.

CLAIM UNDER TEST: the in-tree rigidity chain (bridgeZ_bounded -> RepK) only ever feeds
BoundedHalfBasisIndep coefficient vectors of the form  g_j = contribZ A j - contribZ B j,
where A,B are FINSETS of signed half-basis points. Since fiber(A,j) subset {(j,T),(j,F)} and
isgn(j,T)=+1, isgn(j,F)=-1, the achievable per-index contribZ is:
    empty -> 0,  {(j,T)} -> +1,  {(j,F)} -> -1,  {both} -> 0.
=> contribZ A j  in  {-1, 0, +1}.  Hence the REALIZABLE coefficient vector is
    g_j = a_j - b_j,  a_j, b_j in {-1,0,1}   =>   g_j in {-2,-1,0,1,2}.

So the chain needs only:  no nonzero REALIZABLE g (entries in {-2..2}) with
sum_j g_j omega^j = 0 mod p.  Call its minimal height the REALIZABLE C*_real.

The 032525 refutation used g=(-4,-4,-4,-1,-1,-1,0,0) -- max|coeff|=4, NOT a realizable
contribZ-difference (those are bounded by 2). So that witness is OFF-SPEC for the chain.

QUESTIONS:
 (R1) Is there a nonzero {-2..2}^N relation (realizable height) at the prize regime n=2^a, p~n^4?
      If YES at small n -> chain genuinely breaks (real wall). If NO -> 032525 over-claimed the break.
 (R3) Thinness (rule 3): is the realizable minimal height larger for thin 2-power omega vs thick?

Exact integer arithmetic. Brute over {-2..2}^N (N=n/2). N<=8 (n<=16) brute is 5^8=390625, trivial.
"""
import sys
from itertools import product

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
        if pow(r, n // 2, p) != 1 and pow(r, n, p) == 1:  # primitive 2^m-th
            return r
    return None

def powers(omega, N, p):
    return [pow(omega, j, p) for j in range(N)]

def min_height_realizable(omega, N, p, maxC=2):
    """Smallest max|coeff| over nonzero relations with entries in [-maxC,maxC].
       Returns (height, witness) or (None, None) if independent up to maxC."""
    pw = powers(omega, N, p)
    for h in range(1, maxC+1):
        for g in product(range(-h, h+1), repeat=N):
            if max(abs(x) for x in g) != h:
                continue
            s = 0
            for j in range(N):
                if g[j]:
                    s = (s + g[j]*pw[j]) % p
            if s % p == 0:
                return h, g
    return None, None

def make_primes(m, betas):
    n = 1 << m
    out = []
    for beta in betas:
        target = int(round(n**beta))
        base = target - (target % n) + 1
        found = None
        for delta in range(0, 4000*n, n):
            for cand in (base+delta, base-delta):
                if cand > n and isprime(cand) and (cand-1) % n == 0:
                    found = cand
                    break
            if found: break
        if found:
            out.append((beta, found))
    return out

def main():
    print("=== probe_407_realizable_bhbi: realizable {-2..2} BHBI height at prize regime ===")
    for m in (3, 4):   # n=8, n=16
        n = 1 << m
        N = n >> 1
        print("\n--- n=%d (N=%d half-basis), 2-power thin subgroup mu_n ---" % (n, N))
        primes = make_primes(m, [2.0, 3.0, 4.0, 5.0])
        for beta, p in primes:
            omega = primitive_2pow_root(p, m)
            if omega is None:
                print("  beta=%.2f p=%d: no primitive root, skip" % (beta, p))
                continue
            half_is_neg1 = (pow(omega, N, p) == (p-1))
            h, g = min_height_realizable(omega, N, p, maxC=2)
            if h is None:
                verdict = "INDEPENDENT up to 2 (chain HOLDS at realizable support)"
                wit = ""
            else:
                verdict = "REALIZABLE RELATION height=%d -> chain BHBI(omega,%d,%d) FALSE" % (h, N, h)
                wit = "  witness g=%s" % (g,)
            print("  beta=%.2f p=%10d  omega^N==-1:%s  ->  %s%s" % (beta, p, half_is_neg1, verdict, wit))

if __name__ == "__main__":
    main()
