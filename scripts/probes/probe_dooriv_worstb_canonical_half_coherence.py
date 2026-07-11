#!/usr/bin/env python3
"""
Door-(iv) Lane-1 PROBE (#444): is the WORST frequency FULLY coherent on the
CANONICAL multiplicative half-split, or is there a real, prime-stable slack?

WHY THIS PROBE (deconfliction + value):
  The coherence-slack ABSTRACT lane is already mapped dead in DISPROOF_LOG: any
  coset-half coherence-saving certificate collapses at a "fully coherent prize-worst
  frequency" (see _DoorIVCoherenceSlackVacuousAtArgmax and the multi-piece sign-mass
  bricks). BUT every one of those refutations has an explicit ESCAPE CLAUSE:
  "...OR prove the worst frequency is NOT fully coherent." Nobody has measured this
  cleanly for the CANONICAL split. The existing probe_444_worstb_coset_arithmetic.py
  uses the EVEN/ODD power split (G[0::2] vs G[1::2]); for the large-|eta| cosets BOTH
  halves are individually near-real-positive so it reports cos=+1.000000000 EXACTLY —
  that is a decomposition ARTIFACT, not the adversarial coherence.

THE CANONICAL SPLIT (geometrically meaningful, NOT even/odd of generator powers):
  mu_n = mu_{n/2} ⊔ (xi * mu_{n/2}), where mu_{n/2} = <h^2> is the index-2 subgroup
  and xi = h is the nontrivial coset rep. So
     eta_b = A_b + B_b,   A_b = Σ_{u∈mu_{n/2}} e_p(b u),   B_b = Σ_{u∈mu_{n/2}} e_p(b xi u).
  This is the split that the Gauss-period / quadratic-subfield recursion actually uses,
  and B_b = A_{b*xi} (a multiplicative SHIFT of the SAME half-sum) — exactly the object
  the Lane-3 _DoorIVMultShiftCollinear bricks are about. The half-coherence is
     cos_half(b) = Re(A_b conj(B_b)) / (|A_b| |B_b|).

MEASURED QUANTITY:
  At the ARGMAX b* (over the quotient F_p^*/mu_n, exact phase sums, prize regime
  p ≈ n^beta with beta≈4, p ≫ n^3, proper PROPER subgroup), report cos_half(b*),
  the coherence DEFICIT (1 - cos_half(b*)), and whether |A|≈|B| (balanced halves).
  Sweep multiple structured/random primes per n to test PRIME STABILITY.

VERDICT LOGIC (honest, falsifiable):
  - If 1 - cos_half(b*) is bounded away from 0 by a prime-stable margin -> the worst
    frequency is NOT fully coherent on the canonical split => the coherence-slack
    escape clause is LIVE (a real, non-vacuous target). REPORT the margin.
  - If cos_half(b*) -> 1 (deficit -> 0) uniformly -> the worst frequency IS fully
    coherent canonically => the refuted-lever family's hypothesis HOLDS and the
    canonical-half coherence-slack route is confirmed dead (a clean constraint).
  Either way it is a result. NO CORE/cancellation/completion/capacity claim is made.

Exact integer phases (no float p arithmetic until the final exp). NEVER validates on
n=q-1. PROPER subgroup mu_n ⊊ F_p^* only.
"""
from __future__ import annotations
import argparse, math, statistics
import numpy as np

TAU = 2.0 * math.pi

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= m: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def primes_for(n, beta, count):
    """count primes p ≡ 1 (mod n), p >= n^beta, p > n (PROPER subgroup)."""
    target = int(n**beta)
    start = ((max(target, n+1)) // n) * n + 1
    out = []
    k = 0
    while len(out) < count and k < 5_000_000:
        cand = start + k*n
        if cand > n and is_prime(cand):
            out.append(cand)
        k += 1
    return out

def primitive_root(p):
    fac = []; pm = p-1; d = 2
    while d*d <= pm:
        if pm % d == 0:
            fac.append(d)
            while pm % d == 0: pm //= d
        d += 1
    if pm > 1: fac.append(pm)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

def scan(n, p, g, topk_search):
    """Exact argmax over the quotient F_p^*/mu_n; canonical half coherence at b*."""
    m = (p-1)//n
    h = pow(g, m, p)                 # generator of mu_n
    mu = np.array([pow(h, t, p) for t in range(n)], dtype=np.int64)
    half = n//2
    h2 = pow(h, 2, p)
    sub = np.array([pow(h2, t, p) for t in range(half)], dtype=np.int64)   # mu_{n/2}=<h^2>
    cosrep = h                       # xi: nontrivial coset rep, mu_n = sub ⊔ h*sub
    # quotient reps b_j = g^j, j=0..m-1.  Exact phase sums; chunk for memory.
    chunk = 4096
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)
    absvals = np.empty(m, dtype=np.float64)
    for lo in range(0, m, chunk):
        rr = reps[lo:lo+chunk]
        ph = (rr[:,None]*mu[None,:]) % p
        v = np.exp(1j*TAU*ph/p).sum(axis=1)
        absvals[lo:lo+len(rr)] = np.abs(v)
    # the (topk_search) worst cosets, compute canonical half coherence for each
    order = np.argsort(absvals)[::-1][:topk_search]
    rows = []
    for j in order:
        b = int(reps[j])
        phA = (b*sub) % p
        phB = (b*(cosrep*sub % p)) % p
        A = np.exp(1j*TAU*phA/p).sum()
        B = np.exp(1j*TAU*phB/p).sum()
        eta = A + B
        absA, absB = abs(A), abs(B)
        denom = absA*absB
        cos_half = (np.real(A*np.conj(B))/denom) if denom else float('nan')
        bal = min(absA, absB)/max(absA, absB) if max(absA, absB) else float('nan')
        rows.append((int(j), float(abs(eta)), float(cos_half), float(bal),
                     float(absA), float(absB)))
    return m, rows

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", type=int, nargs="+", default=[16,32,64])
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--primes", type=int, default=6)
    ap.add_argument("--topk", type=int, default=4)
    args = ap.parse_args()
    print("Door-(iv) Lane-1: CANONICAL half-coherence at the WORST frequency b*")
    print("split: mu_n = mu_{n/2} ⊔ xi*mu_{n/2};  cos_half = Re(A conj B)/(|A||B|)")
    print("question: is cos_half(b*) pinned at +1 (fully coherent) or is there prime-stable slack?\n")
    grand = []
    for n in args.ns:
        if n**args.beta > 8_000_000:
            print(f"n={n}: skip (p≈n^beta too large for exact scan)"); continue
        ps = primes_for(n, args.beta, args.primes)
        print(f"=== n={n}  beta={args.beta}  ({len(ps)} primes p≡1 mod n, p≥n^beta) ===")
        print(f"{'p':>12} {'b*idx':>8} {'|eta|':>9} {'cos_half(b*)':>13} {'1-cos':>10} {'bal|A|/|B|':>11}")
        cos_at_argmax = []
        for p in ps:
            g = primitive_root(p)
            m, rows = scan(n, p, g, args.topk)
            j0, eta0, cos0, bal0, aA, aB = rows[0]   # the actual argmax
            cos_at_argmax.append(cos0)
            print(f"{p:>12} {j0:>8} {eta0:>9.4f} {cos0:>13.9f} {1-cos0:>10.2e} {bal0:>11.4f}")
        if cos_at_argmax:
            cmin = min(cos_at_argmax); cmax = max(cos_at_argmax)
            cmean = statistics.mean(cos_at_argmax)
            defmax = 1-cmin   # largest deficit observed
            defmin = 1-cmax   # smallest deficit
            print(f"  --> cos_half(b*): min={cmin:.9f} mean={cmean:.9f} max={cmax:.9f}")
            print(f"      coherence DEFICIT (1-cos): min={defmin:.3e} max={defmax:.3e}")
            grand.append((n, cmin, cmean, cmax, defmin, defmax))
        print()
    print("=== SUMMARY: is the worst frequency fully coherent on the canonical split? ===")
    print(f"{'n':>4} {'cos_min':>11} {'cos_mean':>11} {'cos_max':>11} {'defmin':>10} {'defmax':>10}")
    for (n, cmin, cmean, cmax, defmin, defmax) in grand:
        print(f"{n:>4} {cmin:>11.7f} {cmean:>11.7f} {cmax:>11.7f} {defmin:>10.2e} {defmax:>10.2e}")
    if grand:
        # trend of the SMALLEST deficit (best case for "fully coherent") as n grows
        defmins = [g[4] for g in grand]
        print("\nVERDICT INPUT: if the *smallest* deficit (1-cos_max) collapses toward 0 as n grows,")
        print("the worst frequency is fully coherent canonically (escape clause DEAD). If it stays")
        print("bounded away from 0 prime-stably, the escape clause is LIVE (real non-coherence slack).")
        print("smallest-deficit-by-n:", [f"{n}:{d:.2e}" for (n,_,_,_,d,_) in grand])

if __name__ == "__main__":
    main()
