#!/usr/bin/env python3
"""
probe_mca_spectrum_mechanism.py  (#389, Fable, 2026-06-12)

THE MECHANISM for delta* = capacity - Theta(1/log n), assembled and verified.

Builds on probe_ld_mca_gap.py.  For the deep-band stacks the direction row is u1 = x^k;
at k=2 that is the parabola x^2, which has NO 3 collinear points, so u1|_S is never
jointly-explainable for |S| >= 3.  Hence for these stacks MCA-bad = LD-bad exactly:
  gamma is MCA-bad at agreement a  <=>  x^e + gamma*x^2 is affine (degree <=1) on some
  a-subset of mu_n  <=>  some a-subset of the (x, x^e + gamma x^2) graph is collinear.

This probe verifies, on mu_16, that the worst-case bad-scalar set is:
  (i)  EXACTLY a union of mu_n-cosets (spectrum-collapse / SPECTRUM=DOMAIN, #371);
  (ii) q-INDEPENDENT: N_a = (#cosets)*n + O(1), flat across q;
  (iii) the #cosets EXPLODES toward capacity (the cliff): a=5 -> 0, a=4 -> 6, a=3 -> 9.

Consequence (the mechanism): N_a = census spectrum = (#mu_n-cosets)*n, q-free.  For
production q (>= poly(n)*2^128) the interior spectrum (O(n log n)) is SILENT (<= eps*.q),
and delta* = the cliff frontier where #cosets explodes = capacity - Theta(1/log n) = KKH26.
Supports the Calibrated Pin with the precise q-independent spectrum mechanism (NOT the
q-decaying witness mass).  Open piece: spectrum-collapse for the beyond-monomial worst case.
"""

def rou(p, n):
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if all(pow(h, d, p) != 1 for d in range(1, n)):
            return [pow(h, i, p) for i in range(n)]

def ld_bad_set(D, e, p, a):
    """{gamma : x^e + gamma x^2 affine on some a-subset of D}  (= MCA-bad for u1=x^2)."""
    n = len(D)
    bad = set()
    for g in range(p):
        w = [(pow(x, e, p) + g * pow(x, 2, p)) % p for x in D]
        seen = {}; found = False
        for i in range(n):
            for j in range(i + 1, n):
                dx = (D[i] - D[j]) % p
                if dx == 0:
                    continue
                al = ((w[i] - w[j]) * pow(dx, p - 2, p)) % p
                be = (w[i] - al * D[i]) % p
                if (al, be) in seen:
                    continue
                seen[(al, be)] = 1
                if sum(1 for t in range(n) if (al * D[t] + be) % p == w[t]) >= a:
                    found = True; break
            if found:
                break
        if found:
            bad.add(g)
    return bad

def cosets_of(B, D, p):
    """# of mu_n-cosets covering the nonzero part of B (verifies coset-closure too)."""
    mu = D
    Bnz = B - {0}
    closed = all(((b * h) % p in B) for b in list(Bnz) for h in mu)
    seen = set(); norb = 0
    for b in sorted(Bnz):
        if b in seen:
            continue
        orb = {(b * h) % p for h in mu}
        seen |= orb; norb += 1
    return norb, closed

if __name__ == "__main__":
    n = 16
    print(f"=== mu_{n}: worst monomial x^9, u1=x^2; N_a = (#cosets)*n + O(1), q-independent ===")
    print(f"{'a':>3} {'delta':>6} {'q=193':>10} {'q=449':>10} {'#cosets':>8}")
    for a in [3, 4, 5]:
        row = []
        cos = None
        for p in (193, 449):
            D = rou(p, n)
            B = ld_bad_set(D, 9, p, a)
            nc, closed = cosets_of(B, D, p)
            row.append(f"{len(B)}({nc}c,{closed})")
            cos = nc
        print(f"{a:>3} {1-a/n:>6.3f} {row[0]:>10} {row[1]:>10} {cos:>8}")
    print("\n145=9*16+1, 97=6*16+1, 1=0+1: bad set is EXACTLY mu_16-cosets (closed=True),")
    print("q-INDEPENDENT, #cosets explodes toward capacity (a=k+1=3) = the CLIFF.")
    print("=> delta* = 1 - a_min/n, a_min = min{a : (#cosets_a)*n <= eps*.q}; interior silent,")
    print("   cliff binds => delta* = capacity - Theta(1/log n) = KKH26 (Calibrated Pin mechanism).")
