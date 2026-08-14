#!/usr/bin/env python3
"""Bad-prime certificate: compute Norm_{Q(zeta_32)/Q}(delta) for every
distinct witness-dense difference delta = e_w(x0) - e_t(x0) at
non-agreement points x0 (all nonzero in Z[zeta_32] per char0.py).

The exactness law fails at a split prime p iff p divides one of these
norms (Galois closure argument; the configuration set is stable under
Gal composed with the mirror isomorphism x -> zeta^8 x, lam -> -lam).

Outputs: number of distinct deltas, certificate that BabyBear and p2
divide none of the norms, and all 'small' split-prime divisors
(p = 1 mod 32, p < 2*10^6) -> predicted violating primes for sweep.py.
"""
import json
from itertools import combinations
from char0 import (N, ZERO, ONE, zpow, add, sub, neg, mul, mul_zpow,
                   witness_list, dense_list)


def galois(v, j):
    """sigma_j: zeta -> zeta^j (j odd)."""
    out = [0] * N
    for i, c in enumerate(v):
        if c:
            k = (i * j) % 32
            if k < 16:
                out[k] += c
            else:
                out[k - 16] -= c
    return tuple(out)


def norm(v):
    acc = ONE
    for j in range(1, 32, 2):
        acc = mul(acc, galois(v, j))
    # must be a rational integer
    assert all(c == 0 for c in acc[1:]), acc
    return acc[0]


def main():
    wits = witness_list()
    dens, _ = dense_list(verbose=False)
    dlist = list(dens.values())
    deltas = set()
    for w in wits:
        ew, Tw = w['ew'], w['Tw']
        for d in dlist:
            et, Tt = d['ev'], d['Tt']
            for k in range(32):
                if k in Tw or k in Tt:
                    continue
                deltas.add(sub(ew[k], et[k]))
    print(f"distinct deltas: {len(deltas)}")
    assert ZERO not in deltas

    # canonicalize by Galois orbit + sign (norm-invariant)
    canon = set()
    for v in deltas:
        orbit = []
        for j in range(1, 32, 2):
            gv = galois(v, j)
            orbit.append(gv)
            orbit.append(neg(gv))
        canon.add(min(orbit))
    deltas = canon
    print(f"orbit representatives: {len(deltas)}")

    P_BB, P2 = 2013265921, 3221225473
    bb_bad = p2_bad = 0
    small_bad = {}
    # small split primes for divisor scan
    def sieve_primes(lim):
        s = bytearray([1]) * lim
        s[0:2] = b'\x00\x00'
        for i in range(2, int(lim ** .5) + 1):
            if s[i]:
                s[i * i::i] = bytearray(len(s[i * i::i]))
        return [i for i in range(lim) if s[i]]
    small_split = [q for q in sieve_primes(2 * 10 ** 6) if q % 32 == 1]
    print(f"scanning {len(small_split)} split primes < 2e6 as divisors")

    norms = []
    maxabs = 0
    for v in deltas:
        n = norm(v)
        norms.append(n)
        a = abs(n)
        maxabs = max(maxabs, a)
        if n % P_BB == 0:
            bb_bad += 1
        if n % P2 == 0:
            p2_bad += 1
    print(f"max |norm| = {maxabs:.3e}" if maxabs < 1e308 else
          f"max |norm| has {len(str(maxabs))} digits")
    print(f"norms divisible by BabyBear: {bb_bad}")
    print(f"norms divisible by p2:       {p2_bad}")

    for q in small_split:
        c = sum(1 for n in norms if n % q == 0)
        if c:
            small_bad[q] = c
    print("small split-prime divisors of some norm (q: #norms):")
    for q, c in sorted(small_bad.items()):
        print(f"  {q}: {c}")
    json.dump(dict(n_deltas=len(deltas), bb_bad=bb_bad, p2_bad=p2_bad,
                   max_abs_norm_digits=len(str(maxabs)),
                   small_bad=small_bad),
              open('/tmp/laneA/norms_result.json', 'w'))
    print("saved /tmp/laneA/norms_result.json")


if __name__ == '__main__':
    main()
