"""
PROBE (#444, Shaw's PROMISING creative conj in afdd84d8b): EGF dominance by (1+t)^n.

Shaw observed: Sum_r (n)_r t^r/r! = (1+t)^n  EXACTLY (binomial EGF of the falling factorial (n)_r).
Conjecture: Sum_r [A_r/(2r-1)!!] t^r/r! <= (1+t)^n  for t>=0  => prize.

I test the RIGOROUS/provable LEADING-term version first (my LANE-1 result gives L_r exactly):
   L_r = r! * (n)_r   [leading char-0 term, all-distinct]   (NOTE: (n)_r = n(n-1)...(n-r+1))
   so  L_r/(2r-1)!! * t^r/r! = [r!*(n)_r/(2r-1)!!] * t^r/r! = (n)_r * t^r/(2r-1)!! ... 
   Hmm, Shaw's normalization: L_r/Wick = r!(n)_r/((2r-1)!! n^r) = [r!/(2r-1)!!]*(n)_r/n^r.
   The clean object is  Sum_r (n)_r t^r / r! = (1+t)^n  -- the LEADING coefficient EGF (no Wick).

CLAIM G (provable, exact): Sum_{r=0}^{n} (n)_r t^r / r! = (1+t)^n   [(n)_r = descFactorial = n!/(n-r)!].
  Equivalent to Sum_r C(n,r) t^r = (1+t)^n since (n)_r/r! = C(n,r). EXACT binomial theorem.

CLAIM H: the leading-term normalized EGF  Sum_r [L_r/Wick] t^r/r!  vs  Sum_r [A_r/Wick] t^r/r!  vs (1+t)^n.
  Test numerically whether Sum [A_r^char0/Wick] t^r/r! <= (1+t)^n  (the EGF-dominance, prize-true side).
"""
import math, random
from collections import Counter

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def descfac(n, r):
    p = 1
    for j in range(r):
        p *= (n - j)
    return p

def char0_energy(S, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[v + x] += m
        c = nc
    return sum(m * m for m in c.values())

# CLAIM G: exact binomial EGF of the falling factorial
print("CLAIM G: sum_{r=0}^{n} (n)_r t^r/r!  ==  (1+t)^n  (exact binomial):")
allG = True
for n in [4, 6, 8, 10]:
    for t in [0.3, 1.0, 2.5]:
        lhs = sum(descfac(n, r) * t ** r / math.factorial(r) for r in range(n + 1))
        rhs = (1 + t) ** n
        ok = abs(lhs - rhs) < 1e-7 * max(1, rhs)
        if not ok:
            allG = False
            print(f"  n={n} t={t}: lhs={lhs:.6g} rhs={rhs:.6g} MISMATCH")
print(f"  CLAIM G exact for all tested: {allG}")
print()

# CLAIM H: EGF-dominance of the normalized char-0 energy by (1+t)^n
print("CLAIM H: sum_r [A_r^char0/Wick] t^r/r! <= (1+t)^n  (prize-true EGF dominance):")
random.seed(5)
allH = True
for n in [8, 12, 16]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    R = min(n, 9)
    AoverW = {0: 1.0}  # A_0/Wick = 1 (Wick_0 = empty prod = 1, A_0 = 1)
    for r in range(1, R + 1):
        AoverW[r] = char0_energy(S, r) / (dfac(r) * n ** r)
    for t in [0.2, 0.5, 1.0]:
        lhs = sum(AoverW[r] * t ** r / math.factorial(r) for r in range(R + 1))
        rhs = (1 + t) ** n
        ok = lhs <= rhs + 1e-9
        margin = rhs - lhs
        if not ok:
            allH = False
        print(f"  n={n:>2} t={t}: EGF_partial={lhs:.5f} (1+t)^n={rhs:.5f} dominated={ok} margin={margin:.4f}")
    print()
print(f"  CLAIM H (partial-sum dominance, r up to {R}) holds for all tested: {allH}")
print("  NOTE: partial sums understate the full EGF; this only checks the truncated dominance.")
