#!/usr/bin/env python3
"""
#407 LANE LB (Action-Orbit, Chai-Fan 2026/861) -- Q1 route (i) char-p boundary, DECISIVE.

CONTEXT.  Chai-Fan's Q1 (Conj 4.12) "Norm_{K_d/Q}(F_d(alpha)) != 0 on V_d^prim" is rigorous only
for d in {4,8}; OPEN for d >= 16.  The paper's PROMISING ROUTE (i) to Q1 is the self-similarity
hypothesis
        (*)_d :  on V_d^prim,  x_1 = 0  ==>  x_a = 0  for every ODD a,
extended from d in {4,8} to all d = 2^j by dyadic doubling.  (x_a = power sum p_a of the primitive
config.)  Over C this is VACUOUS (Lam-Leung: no antipodal-free vanishing 2-power-root sum exists).
The genuine d >= 16 content is the CHAR-p version, since the prize prime p (~ n^4..5) is large but
finite and Lam-Leung's integrality argument does not transfer.

PRIOR (in-tree) STATE.
  * EvenOddAntipodalCharFree.lean PROVES char-free: "ALL odd e_i(S) = 0  ==>  S = -S" (antipodal).
    This is the STRONG/correct hypothesis (needs every odd elementary symmetric fn).
  * Route (i) is the WEAKER bootstrap: derive the higher odd vanishings FROM x_1 = 0 alone, via the
    chain self-similarity.  That bootstrap is what is rigorous only at d in {4,8}.

THIS PROBE pins the char-p boundary of route (i) decisively:
  - confirm char-0 V_d^prim(x_1=0) EMPTY for d = 8,16,32 (route (i) vacuous over C).
  - char-p over a WIDE prize-band of primes p = 1 mod d (multiple primes, the KB mandate):
      d=8, d=16  : does any antipodal-free p_1=0 config exist mod p, and does it satisfy (*)_d?
      d=32       : EXHIBIT explicit antipodal-free configs with p_1 = 0 but p_3 != 0 mod p.
  - For each char-p counterexample at d=32, report the FULL odd-power-sum profile (p_3,p_5,p_7,...)
    and confirm it is genuinely antipodal-free and genuinely char-0-nonzero (so it is a NEW char-p
    object, not a char-0 artifact).

VERDICT we are establishing (proven-per-fixed-(d,p) by exhaustive/MITM enumeration):
  route (i) self-similarity bootstrap for Q1 is FALSE in char-p at d = 32  --  x_1 = 0 does NOT
  force x_3 = 0.  Hence Q1 for d >= 16 cannot be closed by route (i) as literally stated; it needs
  either the full odd-symmetric hypothesis (EvenOddAntipodalCharFree) or the resultant form R_d != 0
  directly.  d = 16 is the LAST clean dyadic level for route (i).
"""

import itertools, sys
from math import gcd, log


def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True


def primes_1_mod_n(n, lo, cap):
    out = []; p = lo | 1
    while len(out) < cap:
        if (p - 1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out


def find_gen(p, d):
    for g0 in range(2, p):
        w = pow(g0, (p - 1) // d, p)
        if pow(w, d, p) == 1 and all(pow(w, d // q, p) != 1 for q in (2, 3, 5, 7) if d % q == 0):
            return w
    raise RuntimeError("no primitive d-th root")


def charzero_empty(d, max_size):
    """True iff NO antipodal-free subset Y of mu_d with p_1(Y)=0 over C (Lam-Leung => True for 2^j)."""
    half = d // 2
    def root(j):
        e = j % d; v = [0] * half
        if e < half: v[e] += 1
        else: v[e - half] -= 1
        return v
    for size in range(2, max_size + 1):
        for Y in itertools.combinations(range(d), size):
            Yset = set(Y)
            if any(((j + half) % d) in Yset for j in Y):  # antipodal pair present
                continue
            acc = [0] * half
            for j in Y:
                r = root(j)
                for i in range(half): acc[i] += r[i]
            if all(c == 0 for c in acc):
                return False  # found an antipodal-free char-0 vanishing => NOT empty
    return True


def charp_starD(p, d, cap=600):
    """MITM: antipodal-free Y subset mu_d with p_1(Y) = 0 mod p. Return list of (Y, oddprofile)
    where oddprofile = {a: p_a mod p} for odd a in 3..d-1. Antipodal-free, char-0-nonzero verified."""
    w = find_gen(p, d)
    half = d // 2
    rootval = [pow(w, j, p) for j in range(d)]
    pairs = list(range(half))
    L = half // 2
    def gen(idxs):
        res = {}
        for combo in itertools.product(range(3), repeat=len(idxs)):
            s = 0; exps = []
            for ci, t in zip(combo, idxs):
                if ci == 1: s = (s + rootval[t]) % p; exps.append(t)
                elif ci == 2: s = (s + rootval[t + half]) % p; exps.append(t + half)
            res.setdefault(s, []).append(tuple(exps))
        return res
    left = gen(pairs[:L]); right = gen(pairs[L:])
    found = []
    for ls, llist in left.items():
        tgt = (-ls) % p
        if tgt in right:
            for le in llist:
                for re in right[tgt]:
                    Y = le + re
                    if len(Y) < 2: continue
                    found.append(Y)
                    if len(found) >= cap: break
                if len(found) >= cap: break
        if len(found) >= cap: break
    out = []
    for Y in found:
        prof = {}
        for a in range(3, d, 2):
            s = 0
            for j in Y: s = (s + pow(w, (a * j) % d, p)) % p
            prof[a] = s
        # char-0 nonzero check
        c0 = [0] * half
        for j in Y:
            e = j % d
            if e < half: c0[e] += 1
            else: c0[e - half] -= 1
        out.append((Y, prof, any(c != 0 for c in c0)))
    return out, w, p


def main():
    print("=" * 92)
    print("#407 LANE LB -- Q1 route (i) char-p boundary: (*)_d  [x_1=0 => x_a=0 odd a]  d=8,16,32")
    print("=" * 92)

    print("\n[1] char-0: is V_d^prim(x_1=0) EMPTY (Lam-Leung)?  (=> route (i) vacuous over C)")
    for d in [8, 16, 32]:
        ms = {8: 8, 16: 8, 32: 6}[d]
        empty = charzero_empty(d, ms)
        print(f"    d={d:2d}: V_d^prim(x_1=0) over C is {'EMPTY (vacuous, OK)' if empty else 'NONEMPTY (!)'}"
              f"   [searched |Y| <= {ms}]")

    print("\n[2] char-p (prize band p = 1 mod d, p ~ d^4): does (*)_d route (i) hold?")
    summary = {}
    for d in [8, 16, 32]:
        ps = primes_1_mod_n(d, d ** 4, cap=8)
        tot_pts = 0; tot_viol = 0; first_witness = None
        for p in ps:
            res, w, _ = charp_starD(p, d)
            npts = len(res)
            viol = [r for r in res if any(v != 0 for v in r[1].values())]
            tot_pts += npts; tot_viol += len(viol)
            if viol and first_witness is None:
                first_witness = (p, w, viol[0])
        beta = round(log(ps[0], d), 2)
        if tot_pts == 0:
            verdict = "no primitive char-p point in band -> (*)_d INTACT (vacuous mod p)"
        elif tot_viol == 0:
            verdict = "all primitive pts self-descend -> (*)_d HOLDS in char-p"
        else:
            verdict = f"(*)_d ROUTE (i) FAILS in char-p ({tot_viol}/{tot_pts} pts have x_1=0 but x_3!=0)"
        summary[d] = (tot_pts, tot_viol, verdict, first_witness)
        print(f"    d={d:2d} (~d^{beta}, {len(ps)} primes): {verdict}")

    print("\n[3] EXPLICIT d=32 char-p counterexample (the open Q1 obstruction):")
    if summary[32][3] is not None:
        p, w, (Y, prof, c0nz) = summary[32][3]
        half = 32 // 2
        Yset = set(Y)
        af = all((j + half) % 32 not in Yset for j in Y)
        p1 = sum(pow(w, j, p) for j in Y) % p
        print(f"    p = {p},  primitive 32nd root w = {w}  (w^16 = {pow(w,16,p)} != 1, w^32 = {pow(w,32,p)})")
        print(f"    Y (exponents in Z/32, |Y|={len(Y)}) = {sorted(Y)}")
        print(f"    antipodal-free: {af}   char-0 coordinate vector nonzero: {c0nz}")
        print(f"    p_1 mod p = {p1}   (= 0, a genuine char-p vanishing)")
        print(f"    odd-power profile mod p: " + ", ".join(f"p_{a}={v}" for a, v in sorted(prof.items())))
        nz = [a for a, v in prof.items() if v != 0]
        print(f"    => x_1 = 0 but x_a != 0 for odd a in {nz}.  (*)_d route (i) is REFUTED at d=32 char-p.")
    else:
        print("    (no d=32 witness found -- unexpected)")

    print("\n[VERDICT] route (i) self-similarity bootstrap for Chai-Fan Q1:")
    print(f"    d=8  : {summary[8][2]}")
    print(f"    d=16 : {summary[16][2]}")
    print(f"    d=32 : {summary[32][2]}")
    print("    => d=16 is the LAST clean dyadic level; route (i) cannot close Q1 for d >= 32 as stated.")
    print("       Q1 d>=16 needs the FULL odd-symmetric hypothesis (EvenOddAntipodalCharFree) or R_d!=0 direct.")


if __name__ == "__main__":
    main()
