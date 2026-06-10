#!/usr/bin/env python3
"""Probe for the general-L epsMCA interleaved conversion (O78 follow-up).

The O78 entry claims "any future interleaved-list bound L(2delta) converts to
eps_mca <= (1 + 2*delta*n*L)/q with zero plumbing left" -- but only the L = 1
(unique-decoding) instantiation is a theorem.  Before formalizing the general-L
conversion plus its natural-radius hypothesis form, falsify:

C1 (floor lemma, exact rationals, NNReal/Nat truncation semantics):
    ceil((1-2d)*n) <= 2*ceil((1-d)*n) - n   for all n, d on a fine grid,
    where (1-2d), (1-d) truncate at 0 (NNReal) and the outer subtraction is
    Nat-truncated.  This is the bridge from the natural doubled radius
    a0 = ceil((1-2d)*n) to the theorem floor a = 2*ceil((1-d)*n) - n.

C2 (antitone + composition, exhaustive small fields):
    for every stack (f1,f2), every d in the grid, with t = ceil((1-d)n),
    a = 2t - n (Nat sub), a0 = ceil((1-2d)n):
      (i)  a0 <= a                     (floor lemma instance)
      (ii) L(a) <= L(a0)               (interleavedList antitone in the floor)
      (iii) #mcaBad(t) <= 1 + (n-a)*L(a0)   (the natural-radius corollary)
    where L(b) = #interleavedList(C, f1, f2, b) and #mcaBad(t) is the exact
    MCA bad-scalar count (witness-set reduction; full 2^n subset-enumeration
    control on a subsample).

C3 (teeth): count cases with L(a0) >= 2 AND #mcaBad > 1 + (n-a)  -- i.e. where
    the L = 1 form is FALSE and only the general-L bound survives.  If zero
    such cases exist the general theorem is unexercised (report it).

Exit 0 iff all checks pass.
"""

from fractions import Fraction
from itertools import product
import math
import sys

ok = True


def ceil_frac(x: Fraction) -> int:
    return math.ceil(x)


def nn_sub(x: Fraction, y: Fraction) -> Fraction:
    """NNReal truncated subtraction."""
    return max(x - y, Fraction(0))


# ---------------------------------------------------------------- C1: floor lemma
c1_checks = 0
c1_fail = 0
deltas_fine = [Fraction(i, 120) for i in range(0, 157)]  # 0 .. 1.3
for n in range(1, 61):
    for d in deltas_fine:
        a0 = ceil_frac(nn_sub(1, 2 * d) * n)
        t = ceil_frac(nn_sub(1, d) * n)
        a = max(2 * t - n, 0)  # Nat truncated subtraction
        c1_checks += 1
        if not a0 <= a:
            c1_fail += 1
            if c1_fail <= 5:
                print(f"C1 FAIL n={n} d={d}: a0={a0} > a={a} (t={t})")
if c1_fail:
    ok = False
print(f"C1 floor lemma: {c1_checks} (n,delta) points, {c1_fail} failures")

# ------------------------------------------------- C2/C3: exhaustive small codes
P = 3


def span(gens, n):
    code = set()
    k = len(gens)
    for coeffs in product(range(P), repeat=k):
        w = tuple(sum(c * g[i] for c, g in zip(coeffs, gens)) % P for i in range(n))
        code.add(w)
    return sorted(code)


CODES = [
    ("n4_k2_A", 4, span([(1, 1, 1, 0), (0, 1, 2, 1)], 4)),
    ("n4_k2_B", 4, span([(1, 0, 1, 2), (0, 1, 1, 1)], 4)),
    ("n3_k1", 3, span([(1, 1, 2)], 3)),
]

DELTAS = [Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(1, 3),
          Fraction(3, 8), Fraction(1, 2), Fraction(5, 8), Fraction(3, 4)]

c2_checks = 0
c2_fail_a0 = 0
c2_fail_anti = 0
c2_fail_main = 0
c3_general_needed = 0   # L(a0) >= 2 and badcount > 1 + (n-a): L=1 form false
c3_Lge2 = 0
ctrl_checks = 0
ctrl_fail = 0
saturated = 0

for name, n, C in CODES:
    words = list(product(range(P), repeat=n))
    full = (1 << n) - 1
    masks_of = {}  # agreement bitmask of codeword g with word w

    def agree_mask(g, w):
        m = 0
        for i in range(n):
            if g[i] == w[i]:
                m |= 1 << i
        return m

    # precompute parameter sets per delta
    params = []
    for d in DELTAS:
        t = ceil_frac(nn_sub(1, d) * n)
        a = max(2 * t - n, 0)
        a0 = ceil_frac(nn_sub(1, 2 * d) * n)
        params.append((d, t, a, a0))

    ctrl_budget = 300  # stacks getting the full 2^n subset-enumeration control
    stack_idx = 0
    for f1 in words:
        m1 = [agree_mask(g, f1) for g in C]  # g vs f1
        for f2 in words:
            stack_idx += 1
            m2 = [agree_mask(g, f2) for g in C]
            # joint masks for all codeword pairs
            joint = [a_ & b_ for a_ in m1 for b_ in m2]
            joint_pc = [bin(j).count("1") for j in joint]
            # line agreement masks per gamma
            line_masks = {}
            for gamma in range(P):
                w = tuple((f1[i] + gamma * f2[i]) % P for i in range(n))
                line_masks[gamma] = [agree_mask(g, w) for g in C]

            for d, t, a, a0 in params:
                c2_checks += 1
                if not a0 <= a:
                    c2_fail_a0 += 1
                    ok = False
                    continue
                La = sum(1 for pc in joint_pc if pc >= a)
                La0 = sum(1 for pc in joint_pc if pc >= a0)
                if La > La0:
                    c2_fail_anti += 1
                    ok = False
                # exact bad count, witness-set reduction:
                # gamma bad iff exists c in C with |A_c| >= t and
                # no joint pair covering A_c
                bad = 0
                for gamma in range(P):
                    lm = line_masks[gamma]
                    isbad = False
                    for cm in lm:
                        if bin(cm).count("1") >= t:
                            if not any(j & cm == cm for j in joint):
                                isbad = True
                                break
                    if isbad:
                        bad += 1
                rhs = 1 + (n - a) * La0
                if bad > rhs:
                    c2_fail_main += 1
                    ok = False
                    if c2_fail_main <= 5:
                        print(f"C2 FAIL {name} f1={f1} f2={f2} d={d}: "
                              f"bad={bad} > {rhs} (a={a},a0={a0},La0={La0})")
                if bad == rhs:
                    saturated += 1
                if La0 >= 2:
                    c3_Lge2 += 1
                    if bad > 1 + (n - a):
                        c3_general_needed += 1

                # control: full subset enumeration of mcaBadSet on a subsample
                if stack_idx <= ctrl_budget:
                    badF = 0
                    for gamma in range(P):
                        lm = line_masks[gamma]
                        isbad = False
                        for S in range(full + 1):
                            if bin(S).count("1") < t:
                                continue
                            if not any(cm & S == S for cm in lm):
                                continue
                            if not any(j & S == S for j in joint):
                                isbad = True
                                break
                        if isbad:
                            badF += 1
                    ctrl_checks += 1
                    if badF != bad:
                        ctrl_fail += 1
                        ok = False
                        if ctrl_fail <= 5:
                            print(f"CTRL FAIL {name} f1={f1} f2={f2} d={d} "
                                  f"gamma-counts witness={bad} full={badF}")

print(f"C2: {c2_checks} (stack,delta) checks over {len(CODES)} codes; "
      f"a0-fail={c2_fail_a0} antitone-fail={c2_fail_anti} main-fail={c2_fail_main}; "
      f"saturated={saturated}")
print(f"CTRL: {ctrl_checks} full-enumeration controls, {ctrl_fail} mismatches")
print(f"C3: L(a0)>=2 in {c3_Lge2} cases; general-L strictly needed "
      f"(bad > 1+(n-a), i.e. L=1 form false) in {c3_general_needed} cases")

if c3_general_needed == 0:
    print("C3 WARNING: general-L regime never strictly needed in this sweep "
          "(bound never exceeded the L=1 form) -- theorem still safe, "
          "but report honestly.")

print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
