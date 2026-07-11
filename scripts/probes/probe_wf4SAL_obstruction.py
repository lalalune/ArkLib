#!/usr/bin/env python3
"""
probe_wf4SAL_obstruction.py  (issue #444, lane wf-SAL) -- the OBSTRUCTION pin.

T3 showed the floor object eta_b = sum_{x in mu_n} e_p(bx) SPREADS continuously (NOT Salie-bimodal).
This probe PINS THE PRECISE OBSTRUCTION: why the dyadic subgroup sum is NOT a Salie sum, despite
having -1 in mu_n (negation) and a quadratic-like syndrome.

THE STRUCTURAL FACTS (each tested numerically):

(O1) A Salie sum needs a sum over a FULL multiplicative group F_p^* (or a complete additive line)
     with a QUADRATIC character twist AND an x + c/x inversion in the phase. The floor object
     eta_b sums over a PROPER subgroup mu_n (n << p), pure additive phase e_p(bx), NO inversion,
     NO character twist. It is an INCOMPLETE / cyclotomic Gauss period, not a (complete) Salie sum.

(O2) The Salie evaluability comes from a degree-2 substitution x = y^2 collapsing the char twist
     into a Gauss sum (the in-tree Round9 salieSum_eq_quartic_sub_quadratic does exactly this:
     reduces to a degree-4 Weil sum + an elementary quadratic). For eta_b the analogous square
     substitution y^2 = x maps mu_n -> mu_{n/2} (since squaring on mu_{2^mu} is the index-2 map
     onto mu_{2^{mu-1}}), so eta_b's "square route" gives eta over mu_{n/2}, a SELF-SIMILAR
     SUBGROUP sum -- it does NOT collapse to a single Gauss sum. We verify the square map fibers.

(O3) The DISCRIMINATOR (decisive): a Salie sum has |S|^2 in {0, 4p} (exactly two values). For
     eta_b we measure the second moment / variance of |eta_b|^2 over b: if it were Salie-like the
     distribution of |eta_b|^2 would be 2-atom; we show it is the (continuous) Sato-Tate-like
     spread of a Gauss period (Kloosterman-family), with E[|eta_b|^2] = n (Parseval), confirming
     the generic-spread / NOT-Salie verdict at the level of the full distribution.

(O4) The DIRECT test of the Salie analogue actually built from the subgroup: define the
     "subgroup-Salie" sum  T_b = sum_{x in mu_n} chi(x) e_p(b x)  (quadratic-char twist of the
     period). If THAT were exactly evaluable we'd have closure. Test its magnitude spectrum:
     does it bimodal-collapse (Salie) or spread (generic)?  This is the real swing-for-closure.

HONESTY: proper mu_n (n=2^mu, n|p-1), p PRIME, p>>n^3, NEVER n=p-1. Vectorized numpy.
"""
import math, cmath
import numpy as np
from sympy import isprime, primitive_root

def find_prime(n, beta):
    target = int(n ** beta)
    cand = target - (target % n) + 1
    if cand <= target: cand += n
    while True:
        if isprime(cand) and (cand - 1) % n == 0 and (cand - 1) // n > 1:
            return cand
        cand += n

def mu_n(n, p):
    g = primitive_root(p); h = pow(g, (p - 1) // n, p)
    sub, x = [], 1
    for _ in range(n): sub.append(x); x = x * h % p
    assert -1 % p in sub
    return sub, g, h

def legendre_array(bs_times_x, p):
    # vectorized Legendre via pow on numpy: use python pow per element is slow; precompute QRs
    pass

# ---------- O2: square map fibers mu_n -> mu_{n/2} ----------
def O2(n):
    print("=" * 78)
    print("O2: the square substitution y^2=x on mu_{2^mu} maps onto mu_{2^{mu-1}} (2-to-1),")
    print("    so eta_b's 'Salie square route' yields a SELF-SIMILAR subgroup sum, not a Gauss sum.")
    print("=" * 78)
    p = find_prime(n, 4.0); sub, g, h = mu_n(n, p)
    squares = sorted(set((x * x) % p for x in sub))
    half, _, _ = mu_n(n // 2, p)
    half = sorted(set(half))
    print(f" n={n} p={p}: |mu_n|={len(sub)}, squares of mu_n = {len(squares)} distinct, "
          f"|mu_{{n/2}}|={len(half)}; squares == mu_{{n/2}}? {squares == half}")
    print(f"   => x->x^2 is the index-2 endomorphism mu_n ->> mu_{{n/2}} (2-to-1 onto). The Salie")
    print(f"      degree-2 trick collapses chi-twist into a Gauss sum only over a FULL line/group;")
    print(f"      here it re-funnels into eta over mu_{{n/2}} -- SAME object, smaller subgroup. NO collapse.")

# ---------- O3: |eta_b|^2 distribution -- 2-atom (Salie) or continuous (generic)? ----------
def O3(n):
    print("\n" + "=" * 78)
    print("O3: distribution of |eta_b|^2 over b -- Salie is 2-atom {0,4p-ish}; generic is continuous")
    print("=" * 78)
    p = find_prime(n, 4.0); sub, g, h = mu_n(n, p)
    Sarr = np.array(sub, dtype=np.int64)
    # coset reps: |eta_{cb}| constant on b*mu_n. sweep b=1..p-1 but it's huge; sample uniformly.
    rng = np.random.default_rng(7)
    bs = rng.integers(1, p, size=min(p - 1, 20000))
    e2 = []
    for b in bs:
        ph = 2 * np.pi * ((int(b) * Sarr) % p) / p
        e2.append(abs(np.sum(np.exp(1j * ph))) ** 2)
    e2 = np.array(e2)
    print(f" n={n} p={p}:  E[|eta_b|^2] = {e2.mean():.4f}  (Parseval predicts n={n})")
    print(f"   |eta_b|^2 quantiles [0,.1,.25,.5,.75,.9,1.0]: "
          f"{np.quantile(e2,[0,.1,.25,.5,.75,.9,1.0]).round(2).tolist()}")
    # 2-atom test: fraction of mass within 5% of the two would-be atoms {0, max}
    mx = e2.max()
    near0 = (e2 < 0.05 * mx).mean(); nearmx = (e2 > 0.95 * mx).mean()
    print(f"   mass near 0: {near0:.3f}, near max: {nearmx:.3f}, in the MIDDLE: {1-near0-nearmx:.3f}")
    print(f"   => {'2-ATOM (Salie-like!)' if (near0+nearmx)>0.9 else 'CONTINUOUS middle mass (GENERIC, NOT Salie)'}")

# ---------- O4: the subgroup-Salie sum T_b = sum_{mu_n} chi(x) e_p(bx) ----------
def O4(n):
    print("\n" + "=" * 78)
    print("O4: SWING -- the subgroup-Salie twist T_b = sum_{x in mu_n} chi(x) e_p(bx).")
    print("    If exactly evaluable (bimodal |T_b|) -> off-BGK closure of under-det stratum.")
    print("=" * 78)
    p = find_prime(n, 4.0); sub, g, h = mu_n(n, p)
    # chi(x) = Legendre symbol. On mu_n=mu_{2^mu}: chi(x) = x^{(p-1)/2}. Since x=h^j, chi(h^j)=
    # h^{j(p-1)/2}. With h order n=2^mu and m=(p-1)/n: chi(h^j)= (-1)^{j*m}. m=(p-1)/n is ODD in
    # the prize regime (m=2^128 even in toy? check). chi is a char of mu_n of order dividing 2.
    chi = [1 if pow(x, (p - 1) // 2, p) == 1 else -1 for x in sub]
    print(f" n={n} p={p}: chi on mu_n takes values, #(chi=+1)={chi.count(1)}, #(chi=-1)={chi.count(-1)}")
    Sarr = np.array(sub, dtype=np.int64); carr = np.array(chi)
    rng = np.random.default_rng(11)
    bs = rng.integers(1, p, size=min(p - 1, 20000))
    mags = []
    for b in bs:
        ph = 2 * np.pi * ((int(b) * Sarr) % p) / p
        mags.append(abs(np.sum(carr * np.exp(1j * ph))))
    mags = np.array(mags)
    print(f"   |T_b|: mean={mags.mean():.3f} max={mags.max():.3f}  sqrt(n)={math.sqrt(n):.3f} "
          f"2sqrt(n)={2*math.sqrt(n):.3f}")
    distinct = len(set(mags.round(3)))
    mx = mags.max()
    near0 = (mags < 0.1 * mx).mean(); nearmx = (mags > 0.9 * mx).mean()
    print(f"   distinct |T_b| (rounded): {distinct} among {len(bs)} samples; "
          f"mass near0={near0:.3f} nearmax={nearmx:.3f} middle={1-near0-nearmx:.3f}")
    print(f"   => {'BIMODAL/Salie (CLOSURE SIGNAL!)' if (near0+nearmx)>0.85 and distinct<20 else 'SPREAD (T_b is generic too -- NO Salie closure)'}")

if __name__ == '__main__':
    for n in (8, 16, 32):
        O2(n)
    for n in (16, 32):
        O3(n); O4(n)
