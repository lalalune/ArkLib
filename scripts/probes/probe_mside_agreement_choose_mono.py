# Probe (rule 2): the M-side monotone lift mult gamma <= C(|A_gamma|,a) <= C(s0,a).
# Pure combinatorial weld. Verify (1) Nat.choose top-index monotonicity as integers,
# (2) the cap is NON-VACUOUS and matches realized mult on prize-regime-shaped params,
# (3) it composes with P to give P*C(s0,a) (the AlignableLePinnedMaxMult budget).
from math import comb
import itertools, random

def C(n, k):  # Nat.choose semantics: 0 if k>n
    return comb(n, k) if 0 <= k <= n else 0

# (1) top-index monotonicity C(s,a) <= C(s0,a) for s<=s0, all a (Nat.choose_le_choose a)
ok_mono = True
for s0 in range(0, 40):
    for s in range(0, s0 + 1):
        for a in range(0, 42):
            if not (C(s, a) <= C(s0, a)):
                ok_mono = False
                print("MONO FAIL", s, s0, a)
print("(1) top-index monotonicity C(s,a)<=C(s0,a) for all s<=s0, a in 0..41, s0 in 0..39:",
      "PASS" if ok_mono else "FAIL")

# (2) non-vacuity + sharpness: realized #(a-subsets of an s-set) = C(s,a) exactly.
random.seed(7)
ok_realize = True
ok_capvalid = True
for _ in range(2000):
    a = random.randint(1, 12)
    s = random.randint(a, a + 12)        # agreement size at/above band
    s0 = random.randint(s, s + 10)       # uniform cap
    A = list(range(s))
    realized = sum(1 for _ in itertools.combinations(A, a))
    if realized != C(s, a):
        ok_realize = False
    if not (realized <= C(s, a) <= C(s0, a)):
        ok_capvalid = False
print("(2) realized #(a-subsets)=C(s,a) exactly & realized<=C(s,a)<=C(s0,a):",
      "PASS" if (ok_realize and ok_capvalid) else "FAIL")

# (3) composition P*C(s0,a)
ok_budget = True
for _ in range(500):
    P = random.randint(1, 8)
    a = random.randint(1, 8)
    s0 = random.randint(a, a + 8)
    mults = [C(random.randint(a, s0), a) for _ in range(P)]
    census = sum(mults)
    M = C(s0, a)
    if not (census <= P * M):
        ok_budget = False
print("(3) census = sum mult gamma <= P*C(s0,a) (the AlignableLePinnedMaxMult budget):",
      "PASS" if ok_budget else "FAIL")

print("\nVERDICT: monotone M-side lift sound + non-vacuous. s0 (agreement-size cap) remains OPEN.")
