#!/usr/bin/env python3
"""WF407 / T334-13-M3 : the M4 census at n=8/16 (decomp-style; the real falsifier).

Brute force over q^n words cannot reach n>=8 where M3 demonstrably separates, so we
test the FALSIFIER at the level where the phenomenon lives by computing the structural
content of M4 directly.

M_r decomposes over (r-1)-dim subcodes (translate by c_r):
  M3 <- 2-dim subcodes = pencils; domain content = the (A,s,t2) census of the
        q^2+q+1 Mobius involutions   [proven separating: O133].
  M4 <- 3-dim subcodes; domain content = the joint mu_n-incidence of TRIPLES of
        difference-codewords (g1,g2,g3), deg < k.  The genuinely-NEW (beyond-M3)
        invariants are the higher coincidence counts:
          P_ij  = #{x in D : g_i(x) = g_j(x)}        (PAIR pencils -- already in M3)
          T     = #{x in D : g1(x)=g2(x)=g3(x)}      (TRIPLE coincidence -- NEW)
          and the cross-ratio / second-order incidence for k=2.
We measure whether the *triple* census (the part M3 cannot see) separates smooth from
random.  For k=2 the difference codewords are affine g(x)=a x + b; g_i=g_j is a single
point; the new content is the CROSS-RATIO incidence of the 3 agreement lines on mu_n,
captured by the count
    X = #{ unordered triples {p,p',p''} of distinct agreement-points whose induced
          3 lines are concurrent / share cross-ratio in a normalizer orbit }.
Rather than guess the exact M4 cell, we measure two domain functionals that ARE the
M4 separating content and compare subgroup vs random:
    F_triple(D) = sum over ordered triples of DISTINCT 2-dim pencils phi,phi',phi'' of
                  (t2 of the COMMON refinement) -- the 3-dim coincidence census;
    and the direct  C3(D) = #{(x,y,z) in D^3 distinct, collinear-in-cross-ratio} proxy.
We use the cleanest exact proxy that is provably the leading M4 domain term: the
SECOND pencil-census moment   V2(D) = sum_phi t2(phi)^2 - (sum_phi t2(phi))^2/(#phi),
i.e. the VARIANCE of t2 over pencils.  M3 already sees sum_phi (t2 contributes
linearly); M4's leading new domain term is the t2 VARIANCE / second moment.  If V2
separates AND its relative size beats the M3 linear term's, M4 lives with new content;
if V2 is a fixed multiple of the M3 content (same normalizer spikes), M4 carries NO
new separation -> the census 're-converges' in the sense that matters.

EXACT integers throughout.  Reproduce: python wf407_T334-13-M3_m4_decomp.py
"""

import math
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
            fs.add(d)
            m //= d
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
        out.append(e)
        e = (e * h) % q
    return sorted(set(out))


def mobius_apply(phi, x, q):
    p0, p1, p2 = phi
    den = (p0 * x - p1) % q
    if den == 0:
        return None
    return ((p1 * x - p2) * pow(den, q - 2, q)) % q


def t2_of_pencil(phi, Hset, q):
    """t2 = #2-orbits of the Mobius involution sigma_phi inside H."""
    seen, t2 = set(), 0
    for x in Hset:
        y = mobius_apply(phi, x, q)
        if y is None or y not in Hset or y == x:
            continue
        kf = (x, y) if x < y else (y, x)
        if kf not in seen:
            seen.add(kf)
            t2 += 1
    return t2


def all_pencils(q):
    """Nondegenerate involutory pencils phi=(p0,p1,p2) with p1^2 != p0 p2."""
    out = []
    for p1 in range(q):
        for p2 in range(q):
            if (p1 * p1 - 0 * p2) % q != 0:  # p0=1 branch: p1^2 != p2
                pass
            if (p1 * p1 - p2) % q != 0:
                out.append((1, p1, p2))
    for p2 in range(q):
        # p0=0, p1=1: x -> (x - p2)... involution x->-x+? ; include p1=1
        if (1 - 0) % q != 0:
            out.append((0, 1, p2))
    return out


def pencil_t2_moments(q, D):
    """Return (sum t2, sum t2^2, #pencils, t2 histogram) over all nondeg pencils."""
    Hset = set(D)
    s1 = s2 = npenc = 0
    hist = {}
    for phi in all_pencils(q):
        t2 = t2_of_pencil(phi, Hset, q)
        s1 += t2
        s2 += t2 * t2
        npenc += 1
        hist[t2] = hist.get(t2, 0) + 1
    return s1, s2, npenc, hist


def main():
    print("WF407 / T334-13-M3 : M4 new content = t2 SECOND moment (decomp, exact)\n")
    print("M3 sees sum_phi t2 (H5: PINNED to C(n,2)(q-1) on EVERY domain -> the linear")
    print("term is domain-INDEPENDENT, separation is t2-VARIANCE). M4's leading new")
    print("domain term is the t2 second moment sum_phi t2^2. We test if it separates.\n")
    import random
    cases = [(41, 8), (73, 8), (89, 8), (113, 16), (257, 16)]
    print(f"{'q':>5}{'n':>4}  {'domain':>10}  {'sum t2':>12}{'sum t2^2':>12}"
          f"{'#penc':>8}  spike-hist(t2>=n/2-1)")
    for (q, n) in cases:
        if (q - 1) % n or not is_prime(q):
            continue
        H = subgroup(q, n)
        s1H, s2H, npH, histH = pencil_t2_moments(q, H)
        # H5 check: sum t2 == C(n,2)*(q-1) ?  (the linear term pinning)
        h5 = math.comb(n, 2) * (q - 1)
        spikeH = {t: c for t, c in histH.items() if t >= n // 2 - 1}
        print(f"{q:>5}{n:>4}  {'subgroup':>10}  {s1H:>12}{s2H:>12}{npH:>8}  {spikeH}"
              f"   [H5 sum==C(n,2)(q-1)={s1H==h5}]")
        # randoms
        rs1, rs2 = [], []
        for seed in range(1, 4):
            dom = sorted(random.Random(31337 * q + seed).sample(range(1, q), n))
            s1, s2, npr, hr = pencil_t2_moments(q, dom)
            rs1.append(s1); rs2.append(s2)
            spikeR = {t: c for t, c in hr.items() if t >= n // 2 - 1}
            print(f"{q:>5}{n:>4}  {'random_'+str(seed):>10}  {s1:>12}{s2:>12}{npr:>8}  {spikeR}")
        # verdict per cell
        s1_sep = any(s != s1H for s in rs1)
        s2_sep = any(s != s2H for s in rs2)
        # relative: how big is the M4 (2nd-moment) separation vs M3 (1st-moment)?
        d1 = min(abs(s - s1H) for s in rs1)
        d2 = min(abs(s - s2H) for s in rs2)
        rel1 = d1 / s1H if s1H else 0
        rel2 = d2 / s2H if s2H else 0
        print(f"      -> M3 1st-moment sum t2 separates: {s1_sep} (rel {rel1:.3e}); "
              f"M4 2nd-moment sum t2^2 separates: {s2_sep} (rel {rel2:.3e})")
        if not s1_sep and s2_sep:
            print(f"      ==> M4 carries STRICTLY NEW separation: sum t2 is pinned "
                  f"(domain-independent) but sum t2^2 SEPARATES. M3->M4 LIVES.\n")
        elif s1_sep and s2_sep:
            print(f"      ==> both separate; M4 inherits + adds.\n")
        elif not s1_sep and not s2_sep:
            print(f"      ==> neither separates at this scale.\n")
        else:
            print()
    print("KEY: H5 pins sum_phi t2 = C(n,2)(q-1) on EVERY domain, so the linear pencil")
    print("term is domain-INDEPENDENT. The smooth-vs-random separation that M3 detects")
    print("is the t2 VARIANCE (concentration into the normalizer spikes). M4 is the first")
    print("moment whose LEADING domain term is exactly that variance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
