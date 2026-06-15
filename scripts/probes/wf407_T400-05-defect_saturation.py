#!/usr/bin/env python3
# wf407_T400-05-defect_saturation.py
#
# Thread T400-05-defect (#407). The VERDICT pivot.
#
# In sweep_A09_modq_defect.py the near-capacity direction n=32,w=6 (char-0 count = 0)
# showed N(F_q) = q-1 EXACTLY for the small primes q in {97,193,257,353,449,577}:
#   the halo-carrier RISE FILLS the entire residue field. This is the alarming signal:
#   the mod-q defect is not a thin correction, it can inflate the count to the maximum.
#
# CRITICAL QUESTION (settles controllability):
#   Is "N(F_q) = q-1" a small-prime SATURATION ARTIFACT (the field is just too small to
#   hold more than q-1 values, so ANY direction with >q-1 candidate sets fills it), or is
#   it a genuine structural explosion that persists as q grows past the candidate-set count?
#
#   For n=32, w=6 there are C(32,6) = 906192 candidate sets. As long as q-1 < (number of
#   distinct mod-q e_1 the carriers CAN produce), the count is pinned at q-1 by pigeonhole,
#   NOT by structure. We must run q LARGE (q-1 > #carriers' image) to see the true defect.
#
# This probe:
#   (1) For n=32, w=6: run q from small to LARGE; report N(F_q), q-1, and N(F_q)/(q-1).
#       The defect is "saturated/artifact" while N=q-1; it becomes "genuine structural"
#       when N(F_q) < q-1 and we can read the true carrier-image size.
#   (2) Identify the LARGEST defect (#distinct new e_1) at any single large q = the
#       worst-case-over-q the grand challenge demands, and compare to the MCA budget
#       ceiling ~ q*eps* (here eps* tiny, so budget ~ small).
#   (3) The CONTROLLABILITY verdict: does the worst-case carrier image stay O(n^c) for a
#       fixed c (controllable, sub-capacity) or grow like q (uncontrollable, fills field)?
#
# EXACT enumeration.  Run:  python <thisfile>

import itertools
from sympy import isprime, primitive_root

def e1_vec(A, n):
    h = n // 2
    v = [0] * h
    for a in A:
        a %= n
        if a < h: v[a] += 1
        else: v[a - h] -= 1
    return tuple(v)

def e2_vec_char0(A, n):
    h = n // 2
    v = [0] * h
    L = list(A)
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            e = (L[a] + L[b]) % n
            if e < h: v[e] += 1
            else: v[e - h] -= 1
    return v

def zeta_modq(q, n):
    g = primitive_root(q)
    return pow(g, (q - 1) // n, q)

def eval_modq(v, z, q):
    acc = 0; zp = 1
    for vi in v:
        if vi:
            acc = (acc + vi * zp) % q
        zp = (zp * z) % q
    return acc % q

def modq_carrier_count(n, w, q):
    """#distinct nonzero e_1 over {S : e_2(S)=0 mod q, e_1(S)!=0 mod q}, and #halo-sets."""
    z = zeta_modq(q, n)
    s = set(); halo = 0
    # precompute e1/e2 vectors once isn't possible (per-set), but we stream
    for A in itertools.combinations(range(n), w):
        v2 = e2_vec_char0(A, n)
        if eval_modq(v2, z, q) == 0:
            halo += 1
            e1 = eval_modq(list(e1_vec(A, n)), z, q)
            if e1 != 0:
                s.add(e1)
    return len(s), halo

def primes_1_mod_n(n, lo, hi):
    out = []
    m = (lo - 1)//n
    while True:
        q = n*m + 1
        if q > hi: break
        if q >= lo and isprime(q):
            out.append(q)
        m += 1
    return out

if __name__ == "__main__":
    print("wf407 / T400-05-defect : SATURATION vs GENUINE-STRUCTURE pivot")
    print("="*72)

    # (1) n=16, w=6 across small AND large q : where does N(F_q) DROP below q-1 ?
    n, w = 16, 6
    Ncand = 1
    from math import comb
    Ncand = comb(n, w)
    print(f"\nn={n} w={w}  (#candidate sets = C({n},{w}) = {Ncand}, char-0 count = 0)")
    print(f"  {'q':>7} {'N(F_q)':>7} {'q-1':>7} {'N/(q-1)':>8} {'#halo':>7}  status")
    for q in primes_1_mod_n(n, 17, 4200):
        cnt, halo = modq_carrier_count(n, w, q)
        ratio = cnt/(q-1)
        status = "SATURATED(=q-1)" if cnt == q-1 else ("genuine (<q-1)" if cnt>0 else "clean (0)")
        print(f"  {q:>7} {cnt:>7} {q-1:>7} {ratio:>8.3f} {halo:>7}  {status}")

    # (2) n=32, w=6 : the headline near-capacity direction. small + ONE large q to escape sat.
    n, w = 32, 6
    Ncand = comb(n, w)
    print(f"\nn={n} w={w}  (#candidate sets = C({n},{w}) = {Ncand}, char-0 count = 0)", flush=True)
    print(f"  {'q':>7} {'N(F_q)':>7} {'q-1':>7} {'N/(q-1)':>8}  status", flush=True)
    # small ones (saturated) and ONE larger to escape saturation (q-1 > expected image)
    qs = primes_1_mod_n(n, 97, 700) + [2017]
    for q in qs:
        cnt, _ = modq_carrier_count(n, w, q)
        ratio = cnt/(q-1)
        status = "SATURATED(=q-1)" if cnt == q-1 else ("genuine (<q-1)" if cnt>0 else "clean (0)")
        print(f"  {q:>7} {cnt:>7} {q-1:>7} {ratio:>8.3f}  {status}", flush=True)
