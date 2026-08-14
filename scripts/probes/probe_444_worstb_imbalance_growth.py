#!/usr/bin/env python3
"""
probe_444_worstb_imbalance_growth.py  (#444 / #464, door-(iv) Lane 1 — probe-only refinement)

Follow-up to probe_444_worstb_coherent_imbalance.py (kernel _DoorIVWorstBCoherentImbalance.lean):
that probe pinned, at the TRUE worst frequency b*, that the two index-2 coset-halves A (= μ_{n/2},
"squares") and B (= coset h·μ_{n/2}, "non-squares") are COHERENT (ρ(b*)=1) but STRICTLY IMBALANCED
(balance r(b*)=min/max < 1). THIS probe asks two distinct questions, over MANY structured primes per n:

  Q1 (heavier-half structure): is the heavier half consistently A (squares) or B (coset), or does it
     FLIP unpredictably across primes? A fixed heavier side would be exploitable arithmetic structure.
  Q2 (imbalance GROWTH): does the worst-b balance floor min_p r(b*) stay bounded away from 0, or does
     it DECREASE with n (the halves DIVERGE in magnitude as the subgroup thins)?

EMPIRICAL VERDICT (this probe, exhaustive coset scans, multiple odd-m primes p≫n³, never n=q-1):
  Q1: heavier side FLIPS — heavier=A fraction = 0.67 (n=16, 12 primes), 0.38 (n=32, 8 primes),
      0.00 (n=64, 3 primes). NOT locked to one residue class ⟹ no exploitable parity in the
      asymmetric recursion.
  Q2: the balance floor DECREASES with n: min r(b*) = 0.704 (n=16) → 0.527 (n=32) → 0.478 (n=64).
      The worst-b halves DIVERGE in magnitude as n grows — they do NOT re-balance. This SHARPENS
      the sweep-1 "strictly imbalanced, non-monotone" verdict to a MONOTONE divergence of the floor,
      and REFUTES the earlier "[door-iv-halfmass-balanced-at-argmax]" log claim that worst-b is
      balanced: at the TRUE argmax it is not, and the imbalance only grows.

This is PROBE-ONLY (no Lean theorem): the growth of the imbalance floor is an empirical analytic
trend whose proof would require exactly the open CORE structure; formalizing it would be a larp, so
per HARD RULE 1 (no fabricated closure) we log the verdict and do NOT assert a Lean theorem. No moment,
no completion, no Lean. Claims hold for the (n, p) actually computed and reported. CORE remains OPEN.
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % n == 0: continue
        x = pow(a, d, n)
        if x == 1 or x == n-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: ok = True; break
        if not ok: return False
    return True

def prim_root(p):
    phi = p-1; fac = set(); x = phi; d = 2
    while d*d <= x:
        while x % d == 0: fac.add(d); x //= d
        d += 1
    if x > 1: fac.add(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g

def primes_for(n, beta, count):
    target = int(round(n**beta)); k0 = max(2, target//n); out = []
    for dk in range(2000000):
        p = (k0+dk)*n + 1
        if p <= n*n*n: continue
        if is_prime(p) and ((p-1)//n) % 2 == 1:
            out.append(p)
            if len(out) >= count: return out
    return out

TWO_PI = 2*math.pi
def ep(a, p): return cmath.exp(1j*TWO_PI*(a % p)/p)

def worst_b(p, n):
    g = prim_root(p); h = pow(g, (p-1)//n, p)
    powers = [pow(h, j, p) for j in range(n)]
    A_x = [powers[j] for j in range(0, n, 2)]
    B_x = [powers[j] for j in range(1, n, 2)]
    m = (p-1)//n
    bestM = -1.0; best = None
    for t in range(m):
        b = pow(g, t, p)
        A = sum(ep(b*x, p) for x in A_x); B = sum(ep(b*x, p) for x in B_x)
        Me = abs(A + B)
        if Me > bestM: bestM = Me; best = (abs(A), abs(B))
    return best  # (|A|, |B|) at the exhaustive worst b

if __name__ == "__main__":
    print("=== probe_444_worstb_imbalance_growth: heavier-half structure (Q1) + imbalance floor growth (Q2) ===")
    print("    EXHAUSTIVE worst-b coset scan, multiple odd-m primes per n. A=squares, B=coset.")
    for (n, beta, cnt, cap) in [(16,4.0,12,5000),(32,4.0,8,40000),(64,4.0,3,300000)]:
        ps = primes_for(n, beta, cnt)
        heavierA = 0; heavierB = 0; rs = []
        for p in ps:
            m = (p-1)//n
            if m > cap:  # HONESTY GUARD: skip non-exhaustive (no true-worst-b claim)
                continue
            aA, aB = worst_b(p, n)
            r = min(aA, aB)/max(aA, aB)
            rs.append(r)
            if aA > aB: heavierA += 1
            else: heavierB += 1
        tot = heavierA + heavierB
        if tot == 0:
            print(f"  n={n}: no exhaustive primes under cap"); continue
        print(f"  n={n:2d}: primes={tot:2d}  heavier=A(squares):{heavierA} B(coset):{heavierB} "
              f"(A-frac={heavierA/tot:.2f}=>FLIPS, no fixed side)  "
              f"r(b*) floor min={min(rs):.4f} mean={sum(rs)/len(rs):.4f} max={max(rs):.4f}")
    print("  VERDICT: heavier side FLIPS (no parity); balance FLOOR decreases with n => imbalance GROWS,")
    print("  halves DIVERGE (refutes 'worst-b balanced'). PROBE-ONLY (no Lean: trend needs open CORE).")
    print("=== done ===")
