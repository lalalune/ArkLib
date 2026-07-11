#!/usr/bin/env python3
"""
probe_dsj_dyadic_defect_robustness.py  (#444, SYMMETRIC-FUNCTION cluster)

ADVERSARIAL TEST of conjecture (D): the GPU-pinned threshold
    s*(n) = n/2 + 1 - 2*(floor(log2 n) - 3)     "PERFECT fit n=8..32"  (THREE points)
claimed to decompose as
    s*(n) = sqrt(rho)*n + 1  -  2*(dyadic tower depth),   rho=1/4, sqrt(rho)*n=n/2,
    tower depth = (log2 n) - 3.

Two adversarial questions, EXACT char-0:
  Q1 (degrees-of-freedom):  a 3-point dataset (n=8,16,32) cannot distinguish slope -2 from any
      other slope+curvature.  Quantify the fit's freedom explicitly.
  Q2 (structural descent):  is the even-m bad structure EXACTLY self-similar down the tower
      (Lam-Leung even parity, the in-tree _DyadicTowerDescent)?  This is the only claim with
      a proof route; verify it exactly at n=16->8 and n=32->16.

Object (the in-tree over-determined incidence; identical to probe_2adic_tower_recursion):
  fhat(A,j,n,h): signed antipode-folded multiplicity of {j*a mod n}.  badcount(n,k,m) = #distinct
  nonzero readout images of windows |A|=k+m with lower freqs 1..m-1 killed.  By SchurLagrangeBridge
  this is the count of over-determined far-line bad scalars at agreement window k+1 with readout
  gap m.  s* = 1 + max agreement reachable by a bad over-det scalar.
"""
import itertools, math

def fhat(A, jj, n, h):
    v = [0]*h
    for a in A:
        e = (jj*a) % n
        v[e % h] += (1 if e < h else -1)
    return tuple(v)

def badcount(n, k, m, cap=4_000_000):
    h = n//2
    w = k + m
    if w > n or w < 0 or k < 0:
        return None
    if math.comb(n, w) > cap:
        return None
    Z = tuple([0]*h)
    vals = set()
    for A in itertools.combinations(range(n), w):
        if all(fhat(A, j, n, h) == Z for j in range(1, m)):
            vals.add(fhat(A, m, n, h))
    vals.discard(Z)
    return len(vals)

def s_star_direct(n, wmax=None):
    """max agreement w=k+m over over-det far lines (m>=1) with a bad scalar.  Bounded windows."""
    best, best_km = -1, None
    top = n if wmax is None else min(n, wmax)
    for w in range(top, 0, -1):
        # C(n,w) feasibility guard
        if math.comb(n, w) > 4_000_000:
            continue
        found = False
        for m in range(1, w+1):
            bc = badcount(n, w-m, m)
            if bc and bc > 0:
                found, best, best_km = True, w, (w-m, m)
                break
        if found:
            return best, best_km
    return best, best_km

def claimed(n):
    return n//2 + 1 - 2*(int(round(math.log2(n))) - 3)

print("="*78)
print("Q1: exact direct s* on small mu_n (feasible exhaustion only)")
print(f"{'n':>4} {'s*_direct':>10} {'(k,m)':>10} {'claimed':>9} {'match':>6} {'s*-n/2':>8}")
data = {}
for kk in (3, 4):                  # n=8,16 (C(16,w)<=12870, fine)
    n = 1<<kk
    ss, km = s_star_direct(n)
    data[n] = ss
    print(f"{n:>4} {ss:>10} {str(km):>10} {claimed(n):>9} {str(ss==claimed(n)):>6} {ss-n//2:>8}")
print(f"  n=32 direct: C(32,~17)~5e8 INFEASIBLE in char-0 exhaustion -> formula UNVERIFIED here.")

print()
print("="*78)
print("Q2: exact even-parity descent (the ONLY provable structural claim)")
print("    badcount(n,k,2m') ?= badcount(n/2,k//2,m')   and   badcount(n,k,odd)?=0")
for kk in (4, 5):                  # n=16->8, 32->16  (need m small, k//2 small => feasible)
    n = 1<<kk
    ok = True; fails = []
    odd_nonzero = []
    skipped = 0
    for k in range(0, min(n, 8)):
        for mp in range(1, 4):
            m = 2*mp
            a = badcount(n, k, m)
            b = badcount(n//2, k//2, mp) if k % 2 == 0 else None
            if k % 2 == 0:
                if a is None or b is None:
                    skipped += 1
                elif a != b:
                    ok = False; fails.append((k, m, a, b))
        for mo in (1, 3):           # odd readout gaps
            ao = badcount(n, k, mo)
            if ao not in (None, 0):
                odd_nonzero.append((k, mo, ao))
    print(f"  n={n}->{n//2}: even-descent holds={ok} (skipped {skipped} infeasible) {('fails='+str(fails[:3])) if fails else ''}")
    print(f"            odd-m nonzero bad readouts: {odd_nonzero[:5] if odd_nonzero else 'NONE (Lam-Leung)'}")

print()
print("="*78)
print("ADVERSARIAL VERDICT")
print(" Q1: The model s*(n) = a*n + b*log2(n) + c has 3 free params; n=8,16,32 give 3 equations.")
print("     => EXACT interpolation for ANY 3 values; 'PERFECT fit' is a tautology, not evidence")
print("        for slope=-2.  The decomposition into 'sqrt(rho)*n + 1 - 2*depth' is one of")
print("        infinitely many; nothing pins the -2 without n>=64.")
print(" Q2: IF the even-parity descent holds exactly (Lam-Leung), the tower self-similarity is")
print("     real and PROVEN in-tree (_DyadicTowerDescent: (Q.comp X^2).coeff(2l)=Q.coeff l).")
print("     But that descent moves the WHOLE spectrum down an octave; it does NOT by itself")
print("     produce a '-2 per octave' on the AGREEMENT THRESHOLD s* -- the threshold is set by")
print("     the ODD/boundary (m=1 Johnson) frequency, which the even descent leaves untouched.")
print(" CONCLUSION: (D) as a *growing* law is unsupported (3-pt fit).  As an O(1) boundary")
print("     correction that VANISHES in delta* (=1/2-1/n+2(log n-3)/n -> 1/2), it is just the")
print("     restatement of (J): over-det incidence rederives Johnson as main term, the dyadic")
print("     enhancement is a +O(log n / n) -> 0 boundary term.  No new growing structure.")
print("="*78)
