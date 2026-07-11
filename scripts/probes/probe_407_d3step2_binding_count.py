#!/usr/bin/env python3
"""probe_407_d3step2_binding_count.py  (#407 attack D3 step-2 -- binding-radius bad count)

THE D3 STEP-2 HONESTY TEST.  The landed identity RatioCensusWeightIdentity.lean gives, for a
RAW line stack (s0, s1) over F_q:
    wt(s0 + gamma*s1) = n - z0 - ratioMult(gamma),
    ratioMult(gamma) = #{i : s1_i != 0, -s0_i/s1_i = gamma},   z0 = #{i: s1_i=0, s0_i=0}.
The new in-tree lemmas farIncidence_eq_ratioMult_level / farIncidence_mul_le_support turn the
far-line incidence at radius w into the high-multiplicity census of the ratio sequence and bound
it PER FIXED LINE by Markov:  incidence(w) * (n - z0 - w) <= wt(s1) <= n.

The MCA far-line incidence at proximity delta counts gamma s.t. u0+gamma*u1 is delta-close to
RS(deg<k).  The closest codeword w_gamma DEPENDS on gamma: s0 = u0 - w_gamma is NOT a single
fixed vector.  So the per-line Markov bound does not directly apply.  The *binding radius* is the
Johnson-scale agreement a = n - w ~ sqrt(k*n) (window interior 1-sqrt(rho) < delta < 1-rho).

TWO COMPETING ROUTES TO BOUND #bad at the binding radius:
  (R-raw)  IF a single fixed surrogate line (s0,s1) had ratioMult(gamma) >= a at EVERY bad gamma:
           #bad <= n/a <= sqrt(n/k)  -- BGK-free, BEATS budget n.   <-- tested by M3.
  (R-dual) the dual-syndrome census (badScalars_card_mul_le_choose, IN TREE):
           #bad <= C(n,k)/C(a,k) = the JOHNSON signature (n/a)^k -- super-poly.  WALL W1.

MEASUREMENTS (smooth mu_n prize-shaped orbits, multi-prime, EXACT brute over F_p; n=8,10 are
decisive and fast -- larger n is the same verdict but C(n,k)-brute-slow):
  M2  exact far incidence I(delta) at binding radius a for the monomial adversary (worst case
      on a smooth orbit) vs predictions n/a (raw) and C(n,k)/C(a,k) (dual/Johnson).
  M3  DECISIVE: per bad gamma, is the closest codeword distinct?  Does the fixed surrogate line
      (u0,u1) carry ratioMult >= a at all bad gamma?

REPRESENTATIVE RESULT (seen at n=8,10):
  n=8  k=2 a=4:  I=9,  raw n/a=2.0,  dual=4.67.  fixed-surrogate-carries-fibre? NO.
                 #distinct closest codewords / #bad = 9/9 (EVERY bad gamma differs).
  n=10 k=2 a=4:  I=20, raw n/a=2.5,  dual=7.5.   fixed-surrogate? NO.  distinct/bad = 20/20.

VERDICT (honest).  At the binding radius the true incidence I EXCEEDS the raw-Markov prediction
n/a by 4x-10x and tracks/exceeds the dual (Johnson) prediction.  EVERY bad gamma has a DISTINCT
closest codeword and NO fixed surrogate line carries the high ratio fibre at all bad scalars.  So
the per-line first-moment route (farIncidence_mul_le_support) does NOT collapse the MCA count to
sqrt(n/k): the MCA incidence is a UNION over a per-gamma codeword list, and that list size (the
sub-Johnson supply core) is the open content.  The D3-step2 raw-Markov escape is DEAD; only the
dual C(n,k)/C(a,k) Johnson route survives at the binding radius.  This is WALL W1, not capacity.

Exit 0 iff the structural invariants hold (incidence > raw-Markov; per-gamma codewords distinct).
"""
import itertools, sys
from math import comb, isqrt

def isprime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def proot(p):
    for g in range(2, p):
        x=1; o=0
        while True:
            x=x*g%p; o+=1
            if x==1: break
        if o==p-1: return g

def setup(n, plo):
    p = plo
    while not (p % n == 1 and isprime(p)): p += 1
    g = proot(p); h = pow(g, (p-1)//n, p)
    dom = [pow(h, i, p) for i in range(n)]
    assert len(set(dom)) == n
    return p, dom

def inv(a, p): return pow(a, p-2, p)

def interp_eval_full(pts, vals, k, p, dom):
    out = []
    for x in dom:
        tot = 0
        for j in range(k):
            num = den = 1
            for m in range(k):
                if m != j:
                    num = num*((x - pts[m]) % p) % p
                    den = den*((pts[j] - pts[m]) % p) % p
            tot = (tot + vals[j]*num*inv(den, p)) % p
        out.append(tot)
    return out

def closest_codeword_agreement(word, dom, k, p, combos_k):
    best_a = 0; best_supp = None
    n = len(dom)
    for K in combos_k:
        pts = [dom[i] for i in K]; vs = [word[i] for i in K]
        ev = interp_eval_full(pts, vs, k, p, dom)
        A = [i for i in range(n) if ev[i] == word[i]]
        if len(A) > best_a:
            best_a = len(A); best_supp = A
            if best_a == n: break
    return best_a, best_supp

def ratio_mult_at(s0, s1, gamma, p):
    return sum(1 for a,b in zip(s0,s1) if b%p!=0 and (-a*inv(b%p,p))%p == gamma%p)

def far_incidence(u0, u1, dom, k, p, delta_a, combos_k):
    n = len(dom); bad = []
    for gamma in range(p):
        word = [(u0[i] + gamma*u1[i]) % p for i in range(n)]
        a, supp = closest_codeword_agreement(word, dom, k, p, combos_k)
        if a >= delta_a:
            bad.append((gamma, a, supp))
    return bad

def main():
    print("="*78)
    print("D3 STEP-2: binding-radius bad count -- raw-Markov vs dual-census (Johnson)")
    print("="*78)
    FAIL = 0
    for (n, k) in [(8, 2), (10, 2)]:
        rho = k/n
        a = isqrt(k*n)  # Johnson binding radius
        for p_lo in [n*40]:
            p, dom = setup(n, p_lo)
            combos_k = list(itertools.combinations(range(n), k))
            pred_raw  = n / a
            pred_dual = comb(n, k) / max(comb(a, k), 1)
            best_I = 0; best_arg = None
            for au in range(k, n):
                for bu in range(au+1, n):
                    u0 = [pow(x, au, p) for x in dom]
                    u1 = [pow(x, bu, p) for x in dom]
                    bad = far_incidence(u0, u1, dom, k, p, a, combos_k)
                    if 0 < len(bad) < p and len(bad) > best_I:
                        best_I = len(bad); best_arg = (au, bu, bad)
            print(f"\n[n={n} k={k} rho={rho:.3g} p={p}] binding a~sqrt(kn)={a}")
            print(f"   I={best_I}  raw n/a={pred_raw:.2f}  dual C(n,k)/C(a,k)={pred_dual:.2f}"
                  f"  arg={best_arg[:2] if best_arg else None}")
            if best_arg:
                au, bu, bad = best_arg
                u0 = [pow(x, au, p) for x in dom]; u1 = [pow(x, bu, p) for x in dom]
                fixed_ok = all(ratio_mult_at(u0, u1, g, p) >= a for (g,_,_) in bad)
                distinct_w = len({tuple(sorted(s)) for (_,_,s) in bad})
                print(f"   M3: fixed surrogate carries ratioMult>=a at all bad gamma? {fixed_ok}")
                print(f"   M3: #distinct closest codewords / #bad = {distinct_w}/{len(bad)}")
                # invariants for exit code: raw-Markov beaten, codewords all distinct, surrogate fails
                if not (best_I > pred_raw):       FAIL += 1; print("   [VIOLATION] I <= raw n/a")
                if not (distinct_w == len(bad)):  FAIL += 1; print("   [VIOLATION] codewords not all distinct")
                if fixed_ok:                      FAIL += 1; print("   [VIOLATION] surrogate carried fibre")
    print("\nVERDICT: raw-Markov escape DEAD (I >> n/a, per-gamma codewords distinct, no fixed")
    print("surrogate). MCA incidence = union over per-gamma codeword list = sub-Johnson supply")
    print("core (open). Per-line farIncidence_mul_le_support does NOT collapse the count. WALL W1.")
    print("DONE" if FAIL == 0 else f"FAILURES={FAIL}")
    sys.exit(1 if FAIL else 0)

if __name__ == "__main__":
    main()
