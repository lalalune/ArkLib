#!/usr/bin/env python3
"""WF407 / T334-13-M3 : WHICH moment of the t2 distribution first separates?

SURPRISE from wf407_T334-13-M3_m4_decomp: BOTH sum_phi t2 AND sum_phi t2^2 are
domain-INDEPENDENT (identical for subgroup and every random at n=8,16).  Yet M3
separates.  So the separating functional is NOT a low power-sum of t2 alone.

This probe pins the exact structure by computing, for subgroup vs random:
  (a) the power sums  P_r = sum_phi t2^r  for r=1,2,3,4,5  -- which r first separates?
  (b) the JOINT (A,s,t2) profile power content that M3 actually uses (A=common zeros,
      s=support) -- the genuine M3 separating functional.
We also report whether the t2 MAX (sup over pencils) separates -- it is the spike.

EXACT integers.  Reproduce: python wf407_T334-13-M3_t2moments.py
"""

import math
import random
import sys


def is_prime(m):
    if m < 2:
        return False
    f = 2
    while f * f <= m:
        if m % f == 0:
            return False
        f += 1
    return True


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q):
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e); e = (e * h) % q
    return sorted(set(out))


def mobius_apply(phi, x, q):
    p0, p1, p2 = phi
    den = (p0 * x - p1) % q
    if den == 0:
        return None
    return ((p1 * x - p2) * pow(den, q - 2, q)) % q


def pencil_profile(phi, Hset, q):
    """Return (A, s, t2): A=#common zeros (irrelevant for char!=0 mu_n; 0 here since
    0 not in H), s=#support points of the involution in H, t2=#2-orbits."""
    seen, t2, fixed = set(), 0, 0
    supp = 0
    for x in Hset:
        y = mobius_apply(phi, x, q)
        if y is None or y not in Hset:
            continue
        supp += 1
        if y == x:
            fixed += 1
        else:
            kf = (x, y) if x < y else (y, x)
            if kf not in seen:
                seen.add(kf); t2 += 1
    return supp, t2


def all_pencils(q):
    out = []
    for p1 in range(q):
        for p2 in range(q):
            if (p1 * p1 - p2) % q != 0:
                out.append((1, p1, p2))
    for p2 in range(q):
        out.append((0, 1, p2))
    return out


def t2_power_sums(q, D, rmax=5):
    Hset = set(D)
    P = [0] * (rmax + 1)
    joint = {}   # (supp, t2) -> count : the M3 separating profile histogram
    tmax = 0
    for phi in all_pencils(q):
        supp, t2 = pencil_profile(phi, Hset, q)
        for r in range(rmax + 1):
            P[r] += t2 ** r
        joint[(supp, t2)] = joint.get((supp, t2), 0) + 1
        tmax = max(tmax, t2)
    return P, joint, tmax


def main():
    print("WF407 / T334-13-M3 : which t2 moment / profile functional first separates?\n")
    cases = [(41, 8), (73, 8), (113, 16), (257, 16)]
    for (q, n) in cases:
        if (q - 1) % n or not is_prime(q):
            continue
        H = subgroup(q, n)
        PH, jH, tmH = t2_power_sums(q, H)
        rands = []
        for seed in range(1, 4):
            dom = sorted(random.Random(31337 * q + seed).sample(range(1, q), n))
            rands.append(t2_power_sums(q, dom))
        print(f"===== q={q}, n={n} =====")
        print(f"  power sums P_r = sum_phi t2^r :")
        print(f"    {'r':>3} {'subgroup':>16} {'rand1':>16} {'rand2':>16} {'rand3':>16}  separates?")
        for r in range(1, 6):
            row = [PH[r]] + [rr[0][r] for rr in rands]
            sep = any(v != PH[r] for v in row[1:])
            print(f"    {r:>3} {row[0]:>16} {row[1]:>16} {row[2]:>16} {row[3]:>16}  {sep}")
        print(f"  t2 MAX (the spike): subgroup={tmH}  randoms={[rr[2] for rr in rands]}  "
              f"separates={any(rr[2]!=tmH for rr in rands)}")
        # the M3 joint-profile functional: a NONLINEAR statistic over (supp,t2).
        # use sum_phi t2 * C(supp,2) as a representative cross term M3 uses
        def cross(joint):
            return sum(c * t2 * math.comb(s, 2) for (s, t2), c in joint.items())
        cH = cross(jH); cR = [cross(rr[1]) for rr in rands]
        print(f"  M3-type cross functional sum t2*C(supp,2): subgroup={cH} randoms={cR}  "
              f"separates={any(v!=cH for v in cR)}")
        print()
    print("READING: the lowest separating object identifies the moment ladder level.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
