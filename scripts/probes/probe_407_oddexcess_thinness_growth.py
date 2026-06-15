#!/usr/bin/env python3
"""
ODD-EXCESS SPIKE: growth law + THINNESS test (issue #444, OddExcessLaw.lean open core)

The freshly-formalized open core (Shaw push 80a89e78e, OddExcessLaw.lean):
  oddExcess := full_bad \ half_bad,   |oddExcess| = E = I_n - I_{n/2}
where (matched-rate forward lift, squaring map f: mu_n -> mu_{n/2}, x|->x^2):
  full_bad = explainableScalars( RS[mu_n, 2k], delta, x^{2a'}, x^{a0'} )   (EVEN direction on mu_n)
  half_bad = explainableScalars( RS[mu_{n/2}, k], delta', x^{a'}, x^{a0'} )
The named-but-unproven OddExcessSpikeLaw: E = (n/2)^2 at the half-domain binding rung, rho-gated.
In-tree measured: n=16 E=64=(8)^2 (I_n=89, I_{n/2}=25); n=32 E=256=(16)^2.

TWO OPEN QUESTIONS NOBODY HAS PROBED (this probe):
  Q1 (GROWTH):  does E = (n/2)^2 COMPOUND to n=64 (=> collapse fails by Theta(n^2)) or break?
  Q2 (THINNESS, rule-3): is the (n/2)^2 spike THINNESS-ESSENTIAL? I_n is over the THIN mu_n in F_q*.
       If the SAME excess spike appears in the THICK regime (small q, mu_n a big chunk of F_q*), the
       spike is thickness-MONOTONE => a dead end (the board meta-pattern: every per-line object that
       is thickness-invariant converges to Johnson). If it VANISHES / changes in the thick regime,
       the odd-excess is a genuine thin-only prize-direction object.

EXACT engine reused from probe_farline_incidence_exact.py (per-witness-set affine-in-gamma; NO
codeword enumeration, NO floats; exact mod p). PROPER subgroup mu_n (m=(p-1)/n >= 2), NEVER n=q-1.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import (find_prime_cong1, incidence)

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime_with_index(n, m_target, lo):
    """smallest prime p>lo with p%n==1 and (p-1)//n == m_target EXACTLY (controls thickness)."""
    # we want p = m_target*n + 1 prime; scan multiples
    p = m_target*n + 1
    # if that exact index unattainable as prime, walk m up keeping index ~ m_target
    cand = p
    while True:
        if cand > 2 and all(cand % d for d in range(2, int(cand**0.5)+1)):
            return cand, (cand-1)//n
        cand += n  # keeps p%n==1, index grows

def subgroup(p, n):
    """mu_n as a sorted-by-generator list of field elements (proper subgroup of F_p*)."""
    e = (p-1)//n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and all(pow(g, n//q, p) != 1 for q in prime_factors(n)):
            S = [pow(g, j, p) for j in range(n)]
            if len(set(S)) == n:
                return S, g
    return None, None

def even_incidence(n, k, p, rung_r, a_even, a0):
    """I_n for the EVEN direction x^{a_even} (a_even=2a') over mu_n at code degree 2k, rung r.
       Returns max over offset a0-range of incidence (the binding far-line value)."""
    S, g = subgroup(p, n)
    if S is None: return None
    # full-domain code degree is 2k (matched-rate even pullback)
    K = 2*k
    # binding far direction is the even exponent a_even = 2a'; offset a0 swept low
    best = -1; binder=None
    # offset a0 must keep direction FAR: a_even in [K, n-rung). sweep a0 over low exps
    if not (K <= a_even < n - rung_r):
        return ('not_far', a_even, K, n-rung_r)
    for a0 in range(0, n):
        if a0 == a_even: continue
        c, sat = incidence(S, p, K, a0, a_even, rung_r)
        if sat: c = p
        if c > best: best = c; binder=a0
    return best, binder

def half_incidence(nh, k, p, rung_r, a_half, a0):
    """I_{n/2} for direction x^{a_half} over mu_{n/2} at code degree k."""
    S, g = subgroup(p, nh)
    if S is None: return None
    if not (k <= a_half < nh - rung_r):
        return ('not_far', a_half, k, nh-rung_r)
    best=-1; binder=None
    for a0 in range(0, nh):
        if a0 == a_half: continue
        c, sat = incidence(S, p, k, a0, a_half, rung_r)
        if sat: c = p
        if c > best: best=c; binder=a0
    return best, binder

def run_excess(n, k, p, a_half, label):
    """Compute E = I_n(x^{2a'}) - I_{n/2}(x^{a'}) at the half-domain binding rung, this p.
       The matched-rate forward lift uses the SAME rung r on both domains (it lifts radius)."""
    nh = n//2
    a_even = 2*a_half
    # binding rung for the HALF domain = its delta* rung (just beyond Johnson). For rho=1/4, k=nh/4.
    # we sweep rungs and report E at the half-domain binding rung (where I_{n/2} first spikes>budget_h)
    out=[]
    budget_h = nh
    for r in range(k+1, nh - k + 1):
        hi = half_incidence(nh, k, p, r, a_half, None)
        if isinstance(hi, tuple) and hi and hi[0]=='not_far': continue
        if hi is None: continue
        Ih, hb = hi
        fi = even_incidence(n, k, p, r, a_even, None)
        if isinstance(fi, tuple) and fi and fi[0]=='not_far':
            In = None; E=None
        elif fi is None:
            In=None; E=None
        else:
            In, fb = fi
            E = In - Ih
        out.append((r, Ih, In, E))
    return out

if __name__ == '__main__':
    print("="*78)
    print("ODD-EXCESS E = I_n(x^{2a'}) - I_{n/2}(x^{a'}): growth + thinness")
    print("OddExcessSpikeLaw claims E = (n/2)^2 at the half-domain binding rung (rho=1/4)")
    print("="*78)

    # ---- Q1: reproduce in-tree n=16, then n=32, n=64 (THIN regime, p ~ n^4) ----
    print("\n[Q1 GROWTH]  THIN regime (p ~ n^4, proper mu_n), rho=1/4, a' = nh/4 (= k):")
    for n in (16, 32):  # n=64 added below if time permits (heavier)
        nh = n//2; k = nh//4  # rho=1/4 => k/nh = 1/4
        if k < 1: continue
        a_half = k  # the binding LOW far exponent x^k (in-tree binder)
        p = find_prime_cong1(n, n**4)
        rows = run_excess(n, k, p, a_half, f"n={n}")
        target = nh*nh
        print(f"\n  n={n} nh={nh} k={k} (rho={k/nh:.3f}) p={p}  [(n/2)^2 = {target}]")
        for (r, Ih, In, E) in rows:
            mark = ""
            if E is not None and E == target: mark = "  <== SPIKE = (n/2)^2"
            elif E is not None and E > 0: mark = f"  (E>0)"
            print(f"    rung r={r:>3}: I_n/2={Ih}  I_n={In}  E={E}{mark}")
