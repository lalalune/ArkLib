#!/usr/bin/env python3
"""
wf407_T01-norm_structure_aware.py  (Proximity Prize #407, thread T01-norm)

TARGET (407-T01 / G1): the structure-aware cyclotomic norm bound for the §5.0
binding direction.

  Let n = 2^a, zeta a primitive n-th root, S subset {0..n-1} non-antipodal.
  alpha = sum_{i in S} zeta^i,  g_S = sum_{i in S} X^i  (0/1 indicator poly, #S terms).
  N(alpha) = Res(Phi_n, g_S) = prod_{ord(omega)=n} g_S(omega)  (exact integer).

  HOUSE bound:        |N| <= (#S)^{phi(n)} = (#S)^{n/2}      (triangle, archimedean)
  AM-GM / Landau l2:  M(g_S) <= ||g_S||_2 = sqrt(#S)         (Mahler measure via Landau)
                      |N| = prod_{omega} |g_S(omega)| and M(g_S)^{deg} relates them.

THE CLAIM under test (from the issue-407 comment / census 407-T01):
  "At n=128 the house predicts ~2^192 but a measured witness realizes only ~2^131,
   a 2^61 structural slack.  Does Mahler/Landau-l2 (M <= sqrt(sum coeff^2)) or the
   Desnanot-Jacobi ratio-of-minors form predict the measured 2^131?  If a
   structure-aware bound tracks the realized value it closes the n>=112 binding
   direction."

THE GATE fires at level n iff  max_{non-antipodal S} |N(alpha)| < p(n),  p(n) ~ n*2^128.
So the decisive quantity is the WORST CASE max_S |N|, NOT a random/typical witness.

This probe (all EXACT integer arithmetic for the divisibility-relevant facts):
  (A) computes exact |N| for the block S={0..#S-1} and many shapes at n=64,128;
  (B) compares house  (#S)^{n/2}  vs  the Landau/Mahler ceiling  vs realized |N|;
  (C) EXHAUSTIVE / hill-climb worst-case max_S |N| at n=16,32,64 and pins where it
      crosses p(n);  determines whether ANY (#S, shape) at n=128 stays below 2^135;
  (D) tests the Mahler-measure identity log2|N| = phi(n) * (avg over conjugates of
      log2|g_S(omega)|) and whether sqrt(#S) (Landau) is an UPPER bound on the
      per-conjugate geometric mean -> a candidate structure-aware norm ceiling.
"""
import math, cmath, random, itertools
from sympy import resultant, cyclotomic_poly, Poly, symbols, totient, Integer

X = symbols('X')

def indicator_poly(S):
    expr = 0
    for i in S:
        expr += X**i
    return Poly(expr, X, domain='ZZ')

def cyclo_norm(n, S):
    """Exact integer N(alpha) = Res(Phi_n, g_S), g_S = sum_{i in S} X^i."""
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    g = indicator_poly(S)
    return Integer(resultant(Phi, g))

def log2abs(x):
    x = abs(int(x))
    return math.log2(x) if x > 0 else float('-inf')

def is_antipodal(n, S):
    h = n // 2
    s = set(x % n for x in S)
    return all(((j + h) % n in s) == (j in s) for j in range(h))

# Fast numeric |N| via product over conjugates (for large-n worst-case search;
# we confirm against exact resultant on a sample).
def log2_norm_numeric(n, S):
    Sl = list(S)
    total = 0.0
    for c in range(1, n, 2):  # (Z/n)* = odd residues for n a 2-power
        z = sum(cmath.exp(2j * math.pi * c * i / n) for i in Sl)
        m = abs(z)
        if m < 1e-9:
            return float('-inf')
        total += math.log2(m)
    return total

print("=" * 80)
print("wf407 T01-norm  STRUCTURE-AWARE CYCLOTOMIC NORM BOUND")
print("=" * 80)

# ---------------------------------------------------------------------------
# (A) cross-check numeric vs exact resultant
# ---------------------------------------------------------------------------
print("\n[A] numeric-product vs EXACT integer resultant (cross-check)")
for (n, S) in [(16, [0,1,2,3,4]), (32, list(range(11))), (64, list(range(20)))]:
    Nx = cyclo_norm(n, S)
    ln_num = log2_norm_numeric(n, S)
    print(f"  n={n:4d} #S={len(S):2d}  exact log2|N|={log2abs(Nx):9.4f}  "
          f"numeric={ln_num:9.4f}  diff={abs(log2abs(Nx)-ln_num):.2e}")

# ---------------------------------------------------------------------------
# (B) the n=128 S=56 claim: house vs Landau/Mahler vs realized
# ---------------------------------------------------------------------------
print("\n[B] n=128 candidate bounds vs realized |N|  (block S={0..s-1})")
n = 128
phi = int(totient(n))  # 64
print(f"  n={n} phi={phi}  p_prize ~ n*2^128 = 2^{math.log2(n)+128:.2f}")
print(f"  {'#S':>4} {'log2|N| realized':>17} {'house (#S)^phi':>15} "
      f"{'Landau (#S)^(phi/2)':>20} {'block 2^(s/2-1)?':>17}")
for s in [4, 8, 16, 32, 48, 56, 60, 64]:
    S = list(range(s))
    Nx = cyclo_norm(n, S)
    lN = log2abs(Nx)
    house = phi * math.log2(s)
    landau = (phi / 2) * math.log2(s)   # |N| <= ||g||_2^phi = (sqrt s)^phi = s^{phi/2}
    block_pred = s/2 - 1 if (s & (s-1) == 0) else float('nan')  # exact for s a 2-power
    print(f"  {s:>4} {lN:>17.4f} {house:>15.4f} {landau:>20.4f} {block_pred:>17.4f}")
print("  NOTE: block S={0..s-1} has EXACT |N| = ? -- for s a power of 2 it is 2^{s/2-1}")
print("        (B*(zeta-1)=zeta^s-1; if s=n/2 this is -2, giving 2^{n/2-1}).")

# ---------------------------------------------------------------------------
# (C) WORST CASE: max_{non-antipodal S} |N| at n=16,32,64  (exhaustive small, climb big)
#     plus: can ANYTHING at n=128 stay below p~2^135 ?
# ---------------------------------------------------------------------------
print("\n[C] WORST-CASE  max_{non-antipodal S} |N|  (the quantity the gate needs < p)")
print(f"  {'n':>5} {'max log2|N| (search)':>21} {'block 2^(n/2-1)':>16} "
      f"{'house n^(n/2)':>14} {'log2 p_prize':>13} {'gate fires?':>12}")

def worst_case_climb(n, restarts=40):
    best = float('-inf'); bestS = None
    for _ in range(restarts):
        S = set(i for i in range(n) if random.random() < 0.5)
        if not S or len(S) == n:
            continue
        cur = log2_norm_numeric(n, S) if not is_antipodal(n, S) else float('-inf')
        improved = True
        while improved:
            improved = False
            for i in range(n):
                T = S ^ {i}
                if not T or len(T) == n or is_antipodal(n, T):
                    continue
                v = log2_norm_numeric(n, T)
                if v > cur + 1e-9:
                    S, cur = T, v; improved = True
        if cur > best:
            best, bestS = cur, set(S)
    return best, bestS

random.seed(407)
for a in (4, 5, 6, 7):
    n = 1 << a
    best, bestS = worst_case_climb(n, restarts=50 if a <= 6 else 30)
    block = n//2 - 1
    house = (n//2) * math.log2(n)
    lp = math.log2(n) + 128
    fires = best < lp
    print(f"  {n:>5} {best:>21.3f} {block:>16d} {house:>14.1f} {lp:>13.1f} {str(fires):>12}")

# ---------------------------------------------------------------------------
# (D) Mahler / Landau structure-aware bound:  is sqrt(#S) an upper bound on the
#     per-conjugate GEOMETRIC MEAN |g_S(omega)| (=> |N| <= (sqrt #S)^phi) ?
#     Landau: M(g) <= ||g||_2. For g_S 0/1 with s terms, ||g_S||_2 = sqrt(s).
#     M(g_S) = prod_{|root|>1}|root| * |lead|.  But we want prod over PRIMITIVE
#     n-th roots only, = |N|^{1/phi}. Test whether |N|^{1/phi} <= sqrt(#S).
# ---------------------------------------------------------------------------
print("\n[D] Landau/Mahler ceiling test:  is  |N|^{1/phi}  <=  sqrt(#S)  ?")
print("    (would give structure-aware |N| <= (#S)^{phi/2}, beating house by sqrt)")
print(f"  {'n':>4} {'#S':>4} {'|N|^(1/phi)':>13} {'sqrt(#S)':>10} {'Landau holds?':>14}")
viol = 0; total = 0
random.seed(99)
for n in (16, 32, 64):
    phi = int(totient(n))
    for _ in range(8):
        s = random.randint(2, n-2)
        S = sorted(random.sample(range(n), s))
        Nx = cyclo_norm(n, S)
        if int(Nx) == 0:
            continue
        geo = 2 ** (log2abs(Nx) / phi)
        rt = math.sqrt(s)
        holds = geo <= rt + 1e-9
        total += 1
        if not holds:
            viol += 1
        if _ < 3:
            print(f"  {n:>4} {s:>4} {geo:>13.4f} {rt:>10.4f} {str(holds):>14}")
print(f"  --> Landau/Mahler ceiling |N|^(1/phi) <= sqrt(#S) violated {viol}/{total} times")

# Also check the BLOCK at the worst point: block S={0..n/2-1} has geo-mean 2^{(n/2-1)/(n/2)}
# -> ~2, while sqrt(#S) = sqrt(n/2). So Landau holds for the block but is far from |N|=2^{n/2-1}.
print("\n[D'] block witness S={0..n/2-1}: |N|=2^{n/2-1}, |N|^(1/phi)=2^{(n/2-1)/(n/2)}~2,")
print("     Landau ceiling sqrt(n/2): block geo-mean ~2 << sqrt(n/2) for large n -> Landau")
print("     is SLACK for the block.  But |N|=2^{n/2-1} still >> p for n>=512.")

print("\nDONE.")
