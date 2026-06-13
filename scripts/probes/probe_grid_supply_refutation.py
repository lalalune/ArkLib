#!/usr/bin/env python3
"""
probe_grid_supply_refutation.py  (#389, Fable lane, 2026-06-12)

CLAIM UNDER TEST: the announced "mean-degree law" final form of issue #389:
    For any word w (capped large-agreement family), Sigma_c a_c <= 2n
    over lines (k=2) with agreement a_c >= t, pairwise agreement <= 1.
This was measured only at n <= 20 (below the Szemeredi-Trotter onset n ~ t^3).

COUNTERMODEL CANDIDATE: the sheared-grid word.
  Take the N x N integer grid G = {(i,j) : 0<=i,j<N}.  Shear
  (i,j) |-> (i + (N+1) j, j).  The abscissae i + (N+1)j are pairwise
  distinct (base-(N+1) digits), so the sheared grid is the GRAPH of the word
      w(x) = x div (N+1)   on   D = { i + (N+1)j }  (n = N^2 points).
  Shears are affine bijections of the plane mapping lines to lines and
  preserving incidences, so the t-rich-line statistics of the sheared grid
  equal those of the grid itself: classically Theta(n^2/t^3) t-rich lines
  (the ST extremal), with Sigma a_c ~ n^2/t^2 >> 2n once n >> t^3.

  All collinearity identities are over Z, hence transfer verbatim to F_p
  for every prime p > max coordinate spread; so this is a word over an
  (additive-interval-type) evaluation domain in F_p for all large p.

This probe counts EXACTLY (integer arithmetic, no sampling):
  - all lines with >= t points among the n grid points (slope oo excluded:
    after the shear no two points share an abscissa, i.e. in graph
    coordinates vertical lines never carry 2 points);
  - the rich-line count L_t, the agreement mass u = Sigma_{a_c>=t} a_c,
  - the same restricted to a capped family a_c <= cap (cap = 2t as in the
    fleet's census convention),
  - the core supply S = Sigma C(a_c, t) (uncapped and capped),
and compares with the linear law (2n) and the ST shape (n^2/t^3, n^2/t^2).

Also: a control at the fleet's census scale (N=4, n=16) to confirm the
linear law is invisible there.
"""
from collections import defaultdict
from math import comb, gcd

def grid_rich_lines(N, t):
    pts = [(i, j) for i in range(N) for j in range(N)]
    n = len(pts)
    # canonical line through two points over Q: (A,B,C), Ax+By=C, gcd-normalised
    lines = defaultdict(set)
    for a in range(n):
        x1, y1 = pts[a]
        for b in range(a + 1, n):
            x2, y2 = pts[b]
            A = y2 - y1
            B = x1 - x2
            C = A * x1 + B * y1
            g = gcd(gcd(abs(A), abs(B)), abs(C)) or 1
            A, B, C = A // g, B // g, C // g
            if (A, B) < (0, 0) or (A < 0) or (A == 0 and B < 0):
                A, B, C = -A, -B, -C
            lines[(A, B, C)].add(a)
            lines[(A, B, C)].add(b)
    # vertical lines in GRID coords become ordinary lines after the shear;
    # they have N points each. Lines that are vertical AFTER the shear would
    # need two equal sheared abscissae -- impossible. The shear is
    # (x,y) -> (x+(N+1)y, y), invertible, line-preserving: every grid line
    # (including grid-vertical) is a sheared-graph line. So count all.
    rich = {L: S for L, S in lines.items() if len(S) >= t}
    return n, rich

def report(N, t, cap=None):
    n, rich = grid_rich_lines(N, t)
    if cap is None:
        cap = 2 * t  # k=2, m=t-k-1: cap = 2k+m+1 = t+k = t+2; ALSO report t+2 form below
    capw = t + 2     # the SubJohnsonSupplyResidual cap 2k+m+1 at k=2 (= t+k)
    L = len(rich)
    sizes = sorted((len(S) for S in rich.values()), reverse=True)
    u = sum(sizes)
    u_cap = sum(min(s, cap) for s in sizes)
    # the CAPPED-FAMILY reading: only lines with t <= a_c <= capw
    fam = [s for s in sizes if s <= capw]
    L_fam, u_fam = len(fam), sum(fam)
    S_fam = sum(comb(s, t) for s in fam)
    S_core = sum(comb(s, t) for s in sizes)
    print(f"N={N:3d} n={n:5d} t={t} | L_t={L:6d}  u=Sigma a_c={u:7d} | 2n={2*n:6d}  "
          f"n^2/t^3={n*n//t**3:7d}  n^2/t^2={n*n//t**2:8d} | S=SigmaC(a,t)={S_core:9d}")
    print(f"      CAPPED FAMILY (t <= a_c <= {capw}): L_fam={L_fam:6d}  "
          f"u_fam={u_fam:7d}  S_fam={S_fam:9d}   "
          f"family linear law: {'VIOLATED x%.2f' % (u_fam/(2*n)) if u_fam > 2*n else 'holds'}")
    print(f"      size spectrum (top 12): {sizes[:12]}  "
          f"... #lines of each size: "
          f"{ {s: sizes.count(s) for s in sorted(set(sizes), reverse=True)[:8]} }")
    # The Johnson agreement at k=2 (s = k-1 = 1): t_J = sqrt(2 s n)
    tj2 = 2 * 1 * n
    print(f"      sub-Johnson check: t^2 = {t*t} < 2(k-1)n = {tj2}  -> "
          f"{'SUB-JOHNSON (open range)' if t*t < tj2 else 'covered by CS law'}")
    print(f"      LINEAR LAW Sigma a_c <= 2n: "
          f"{'VIOLATED (x%.2f)' % (u/(2*n)) if u > 2*n else 'holds'}"
          f"   capped: {'VIOLATED (x%.2f)' % (u_cap/(2*n)) if u_cap > 2*n else 'holds'}")
    return n, L, u, u_cap

print("=== control at the fleet's census scale (invisible regime n <= 20-ish) ===")
report(4, 4)
print()
print("=== the ST onset: n ~ t^3 and beyond, t = 4 ===")
for N in (8, 10, 12, 14, 16, 20):
    report(N, 4)
print()
print("=== t = 3 (deeper sub-Johnson, onset n ~ 27) ===")
for N in (6, 8, 10, 12):
    report(N, 3)
print()
print("=== t = 5 ===")
for N in (12, 16, 20):
    report(N, 5)
print()
print("=== scaling check at fixed t=4: u/n should grow ~ n/t^2 (ST), not stay <= 2 ===")
for N in (8, 12, 16, 20, 24):
    n, L, u, ucap = report(N, 4)
    print(f"      u/n = {u/n:.2f}   u_capped/n = {ucap/n:.2f}")
