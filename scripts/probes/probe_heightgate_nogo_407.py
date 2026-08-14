#!/usr/bin/env python3
"""
probe_heightgate_nogo_407.py  (#407)

Burn-down of the OPEN-ACTIONABLE "structure-aware norm bound" lever (c.157/c.159):

  > "the realized n=128 norm (~2^131) is ~2^61 below the house-bound prediction
  >  (~2^192), so a resultant/Newton-polygon norm bound could push the
  >  proved-closed regime well past n=32."

The height gate (HeightGateNormBound.gate_2power_antipodal) certifies
  "p | N(Sigma_S)  ==>  S antipodal"
for EVERY non-antipodal S subset range(n) ONLY WHEN, for every such S,
        |N_{Q(zeta_n)/Q}( sum_{i in S} zeta_n^i )|  <  p .
So the gate closes at level n  <=>  max_{non-antipodal S} |N(Sigma_S)| < p(n),
where the prize prime p(n) = n / eps* = n * 2^128.

QUESTION: does an EXACT / structure-aware norm bound (replacing the loose house
bound (#S)^{phi(n)} = n^{n/2}) push the closed regime toward the prize point
n = 2^30 ?

Galois conjugates: Sigma_S^(c) = sum_{i in S} zeta_n^{c i}, c in (Z/n)* = odds.
  N(Sigma_S) = prod_{c odd} Sigma_S^(c).
For a block S = {0,...,s-1}: Sigma_S^(c) = (zeta^{cs}-1)/(zeta^c-1), so
  |N| = prod_{c odd, 1<=c<n} | sin(pi c s / n) / sin(pi c / n) |.
"""
import math, cmath, random

def log2_norm_block(n, s):
    total = 0.0
    for c in range(1, n, 2):
        num = abs(math.sin(math.pi * c * s / n))
        den = abs(math.sin(math.pi * c / n))
        if num == 0.0:
            return float('-inf')          # block sum vanishes for this conjugate
        total += math.log2(num) - math.log2(den)
    return total

def log2_norm_set(n, S):
    """log2 |N(sum_{i in S} zeta^i)| for an arbitrary exponent set S (numeric)."""
    Sl = list(S)
    total = 0.0
    for c in range(1, n, 2):
        z = sum(cmath.exp(2j*math.pi*c*i/n) for i in Sl)
        m = abs(z)
        if m == 0.0:
            return float('-inf')
        total += math.log2(m)
    return total

def prize_log2_p(n, eps_exp=128):
    return math.log2(n) + eps_exp

def is_antipodal(n, S):
    h = n//2
    Sset = set(x % n for x in S)
    return all(((j+h) % n in Sset) == (j in Sset) for j in range(h))

# ---------- 1. exact block witness: |N| = 2^{n/2 - 1} ----------
print("=== 1. explicit non-antipodal witness  S = {0,...,n/2-1}  (block) ===")
print(f"{'n':>7} {'log2|N(block)|':>15} {'= n/2-1?':>10} {'log2 p':>9} {'|N|<p (gate ok)?':>17}")
for a in range(3, 13):
    n = 1 << a
    lN = log2_norm_block(n, n//2)
    lp = prize_log2_p(n)
    print(f"{n:>7} {lN:>15.4f} {str(abs(lN-(n//2-1))<1e-6):>10} {lp:>9.1f} {str(lN < lp):>17}")
print("  => exact norm of the block is 2^{n/2-1} (proof: Sigma=-2/(zeta-1),")
print("     N(zeta-1)=Phi_{2^a}(1)=2, N(-2)=2^{phi(n)}).  It EXCEEDS the prize")
print("     prime for n >= 512, so the gate's |N|<p contradiction CANNOT fire there.")

# ---------- 2. worst-case search: max_S |N| over non-antipodal S ----------
print("\n=== 2. hill-climb for max_{non-antipodal S} |N|  (vs house bound) ===")
random.seed(1)
print(f"{'n':>5} {'best log2|N| found':>19} {'block 2^(n/2-1)':>16} "
      f"{'house n^(n/2)':>14} {'AM-GM (#S)^(n/4)':>17} {'log2 p':>8}")
for a in (4, 5, 6, 7):
    n = 1 << a
    best = float('-inf'); bestS = None
    # random restarts + greedy flips, keep S non-antipodal and nonempty/non-full
    for _ in range(60):
        S = set(i for i in range(n) if random.random() < 0.5)
        if not S or len(S) == n: continue
        cur = log2_norm_set(n, S) if not is_antipodal(n, S) else float('-inf')
        improved = True
        while improved:
            improved = False
            for i in range(n):
                T = (S ^ {i})
                if not T or len(T) == n or is_antipodal(n, T): continue
                v = log2_norm_set(n, T)
                if v > cur + 1e-9:
                    S, cur = T, v; improved = True
        if cur > best:
            best, bestS = cur, set(S)
    house = (n//2)*math.log2(n)
    amgm = (n//4)*math.log2(max(len(bestS),1))   # |N| <= (#S)^{phi/2} = s^{n/4}
    print(f"{n:>5} {best:>19.3f} {n//2-1:>16} {house:>14.1f} {amgm:>17.3f} {prize_log2_p(n):>8.1f}")
print("  => worst-case |N| sits well ABOVE the block, approaching the house;")
print("     finding it IS a sqrt-cancellation / house-maximization problem.")

# ---------- 3. the asymptotic no-go ----------
print("\n=== 3. asymptotic: can ANY norm bound make the gate reach the prize? ===")
print(f"{'n':>12} {'block log2|N| = n/2-1':>22} {'prize log2 p = log2 n +128':>27} {'gate reachable?':>16}")
for a in (5, 8, 10, 15, 20, 30):
    n = 1 << a
    print(f"{n:>12} {n//2-1:>22} {prize_log2_p(n):>27.1f} {str((n//2-1) < prize_log2_p(n)):>16}")
print("""
  The block witness ALONE (exact norm 2^{n/2-1}, an explicit non-antipodal S)
  exceeds the prize prime for all n >= 512, and at the prize point n=2^30 it is
  2^(2^29-1) ~ 2^(5.4e8) >> p ~ 2^158.  Since the gate requires |N(Sigma_S)| < p
  for EVERY non-antipodal S, and this single explicit S already violates it by
  ~5.4e8 bits, NO structure-aware / exact norm bound can rescue the gate at the
  prize point.  An exact bound only extends the closed regime to ~n=256
  (where even the largest |N| first crosses p); it provably cannot approach
  n=2^30.  VERDICT: the height-gate is a small-n shadow; the 'structure-aware
  norm bound' lever does NOT bypass the BGK wall -- the worst-case max_S|N| is
  itself the sqrt-cancellation problem (Section 2 above).
""")
