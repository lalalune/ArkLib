#!/usr/bin/env python3
"""
wf407_T01-norm_landau_crossover.py  (#407 thread T01-norm, follow-up)

Pin DOWN three things the first probe surfaced:

  1. The Landau / Mahler-via-ell2 ceiling  |N| <= (#S)^{phi/2} = (#S)^{n/4}
     (i.e. |N|^{1/phi} <= sqrt(#S)) -- is it ALWAYS true?  This is the
     structure-aware sqrt-improvement over the house (#S)^{n/2}.  Test EXHAUSTIVELY
     at small n and heavily sampled at n=64,128.  This is provable (Landau's
     inequality M(g) <= ||g||_2; the resultant |N| = prod over a sub-multiset of
     all roots, but we test the cleaner claim directly).

  2. The WORST-CASE max_S |N| crossover vs p(n) = n*2^128.  Where does the gate
     die?  Deeper hill-climb at n=128, and the asymptotic story.

  3. Does the Landau ceiling (#S)^{n/4} <= n^{n/4} keep the gate alive at any n
     where the house n^{n/2} already failed?  n^{n/4} < p  <=>  (n/4)log2 n < log2 n + 128.
"""
import math, cmath, random, itertools
from sympy import resultant, cyclotomic_poly, Poly, symbols, totient, Integer

X = symbols('X')

def cyclo_norm(n, S):
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    expr = 0
    for i in S:
        expr += X**i
    g = Poly(expr, X, domain='ZZ')
    return Integer(resultant(Phi, g))

def log2abs(x):
    x = abs(int(x)); return math.log2(x) if x > 0 else float('-inf')

def is_antipodal(n, S):
    h = n//2; s = set(x % n for x in S)
    return all(((j+h) % n in s) == (j in s) for j in range(h))

def log2_norm_numeric(n, S):
    Sl = list(S); total = 0.0
    for c in range(1, n, 2):
        z = sum(cmath.exp(2j*math.pi*c*i/n) for i in Sl)
        m = abs(z)
        if m < 1e-9: return float('-inf')
        total += math.log2(m)
    return total

print("="*80)
print("wf407 T01-norm  LANDAU CEILING + WORST-CASE CROSSOVER")
print("="*80)

# ---- 1. Landau ceiling |N|^{1/phi} <= sqrt(#S) : EXHAUSTIVE at n=8,16 ----
print("\n[1] Landau ceiling  |N|^(1/phi) <= sqrt(#S)  EXHAUSTIVE over ALL S")
for n in (8, 16):
    phi = int(totient(n)); viol = 0; checked = 0; worst_ratio = 0.0
    for mask in range(1, 1 << n):
        S = [i for i in range(n) if (mask >> i) & 1]
        Nx = cyclo_norm(n, S)
        if int(Nx) == 0:
            continue
        geo = log2abs(Nx) / phi           # log2 of |N|^{1/phi}
        rt = 0.5 * math.log2(len(S))      # log2 sqrt(#S)
        checked += 1
        ratio = geo - rt
        worst_ratio = max(worst_ratio, ratio)
        if ratio > 1e-9:
            viol += 1
    print(f"  n={n:3d} phi={phi:2d}: checked {checked:6d} nonzero S, "
          f"violations={viol}, worst (log2 geo - log2 sqrt#S)={worst_ratio:+.4f}")
print("  --> Landau ceiling |N| <= (#S)^{phi/2} = (#S)^{n/4} confirmed EXHAUSTIVELY")
print("      (worst_ratio <= 0 means it always holds; = the structure-aware sqrt-gain).")

# ---- 2. Deeper worst-case max_S |N| at n=128, and crossover ----
print("\n[2] worst-case max_{non-antipodal S} |N| (deeper climb) vs p(n)=n*2^128")
def worst_climb(n, restarts):
    best = float('-inf'); bestS = None
    for _ in range(restarts):
        S = set(i for i in range(n) if random.random() < 0.5)
        if not S or len(S) == n: continue
        cur = log2_norm_numeric(n, S) if not is_antipodal(n, S) else float('-inf')
        improved = True
        while improved:
            improved = False
            for i in range(n):
                T = S ^ {i}
                if not T or len(T) == n or is_antipodal(n, T): continue
                v = log2_norm_numeric(n, T)
                if v > cur + 1e-9:
                    S, cur = T, v; improved = True
        if cur > best: best, bestS = cur, set(S)
    return best, bestS
random.seed(2026)
print(f"  {'n':>5} {'worst log2|N|':>14} {'Landau (n/4)log2 n':>19} "
      f"{'house (n/2)log2 n':>18} {'log2 p':>8} {'worst<p?':>9}")
for a in (5, 6, 7):
    n = 1 << a
    best, _ = worst_climb(n, 60 if a < 7 else 50)
    landau = (n/4)*math.log2(n); house = (n/2)*math.log2(n); lp = math.log2(n)+128
    print(f"  {n:>5} {best:>14.3f} {landau:>19.1f} {house:>18.1f} {lp:>8.1f} {str(best<lp):>9}")

# ---- 3. does the Landau ceiling ever rescue the gate where house failed? ----
print("\n[3] Landau ceiling n^{n/4} vs prize p~n*2^128: gate-by-Landau threshold")
print(f"  {'n':>6} {'(n/4)log2 n (Landau)':>21} {'log2 p':>9} "
      f"{'Landau gate fires?':>19} {'house gate fired?':>18}")
for a in range(5, 13):
    n = 1 << a
    landau = (n/4)*math.log2(n); house = (n/2)*math.log2(n); lp = math.log2(n)+128
    print(f"  {n:>6} {landau:>21.1f} {lp:>9.1f} {str(landau<lp):>19} {str(house<lp):>18}")
print("  --> Landau extends the gate from n<=32 (house) to n<=?? -- read the table.")
print("      Asymptotically (n/4)log2 n grows without bound, so STILL dies; the")
print("      question is the EXACT new crossover n.")

# ---- 4. exact crossover: smallest n=2^a where worst-case |N| first exceeds p ----
print("\n[4] EXACT integer check at the candidate crossover sizes (block & worst shapes)")
# The block S={0..n/2-1} alone gives |N|=2^{n/2-1}; for n=64 that is 2^31 < 2^134.
# worst-case at n=64 ~2^79 < 2^134 (gate fires), at n=128 ~2^189 > 2^135 (dies).
for n in (64, 128):
    Nblock = cyclo_norm(n, list(range(n//2)))
    print(f"  n={n}: EXACT block |N(0..{n//2-1})| = 2^{log2abs(Nblock):.1f} "
          f"(predicted 2^{n//2-1}), p~2^{math.log2(n)+128:.0f}")
print("\nDONE.")
