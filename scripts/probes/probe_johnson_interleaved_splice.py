#!/usr/bin/env python3
"""Probe for the Johnson-interleaved splice (#232, O91 candidate).

The O85 conversion eats ANY uniform interleaved list bound L at the collapse
floor a = 2t - n (t = ceil((1-delta)*n)).  The in-tree Johnson second-moment
bound (JohnsonListBound.lean) is alphabet-generic, and the m=2 interleaved code
C' subset (F^2)^n inherits pairwise agreement <= e = n - d from C (O78's
transfer mechanism).  Candidate chain:

    Lambda_2(a) <= n^2 / (a^2 - n*e)      whenever  n*e < a^2     (pair-Johnson)
    #mcaBad(t)  <= 1 + (n-a)*Lambda_2(a)                          (O74/O85)

giving eps_mca <= (1 + 2*delta*n*L_J)/q on the window n*e < a^2, in real units
delta < (1 - sqrt(e/n))/2 -- strictly wider than O84's unconditional d/(3n) at
low rate, crossover exactly at rho = 1/4.

Falsification targets:
  A. pair-alphabet Johnson cap on EXACT interleaved list sizes (RS over
     F5/F7/F11/F17), every floor a with n*e < a^2, including floors strictly
     OUTSIDE the UD window n + e < 2a (the new content band).
  B. the composed badCount bound at collapse floors a = 2t - n in the
     Johnson-only band (witness-set reduction, exact; full 2^n subset control
     on n <= 6 stacks).
  C. exact window arithmetic, NO floats: (1-r)/3 < (1-sqrt(r))/2 iff r < 1/4
     via the equivalent polynomial sign (4r-1)(r-1) > 0 on Fractions; the
     numeric anchors 0.3232... vs 0.2917 at r=1/8, 0.375 vs 0.3125 at r=1/16;
     and the N-containment UD-window ==> Johnson-gap (4ne <= (n+e)^2 < 4a^2).
  D. teeth: Lambda_2 >= 2 occurs in the Johnson-only band (so the O78 UD lemma
     is FALSE there and only Johnson caps the list), and the gap condition is
     load-bearing (a stack with Lambda_2(a) > n^2 at a floor below the gap).

Exit 0 iff all checks pass.
"""

import random
import sys
from fractions import Fraction
from itertools import product
from math import ceil, isqrt

random.seed(232091)
ok = True


def rs_code(q, n, k):
    """RS code: evaluations of polys deg < k at points 0..n-1 over F_q."""
    pts = list(range(n))
    code = []
    for coeffs in product(range(q), repeat=k):
        w = tuple(sum(c * pow(x, j, q) for j, c in enumerate(coeffs)) % q
                  for x in pts)
        code.append(w)
    return code


def agree_mask(g, w, n):
    m = 0
    for i in range(n):
        if g[i] == w[i]:
            m |= 1 << i
    return m


def max_pairwise_agreement(code, n):
    e = 0
    for i in range(len(code)):
        for j in range(i + 1, len(code)):
            a = sum(1 for x in range(n) if code[i][x] == code[j][x])
            e = max(e, a)
    return e


def make_stacks(code, q, n, count):
    """Random + planted (split between two codewords, fattening the list)."""
    stacks = []
    for _ in range(count // 2):
        f1 = tuple(random.randrange(q) for _ in range(n))
        f2 = tuple(random.randrange(q) for _ in range(n))
        stacks.append((f1, f2))
    half = n // 2
    for _ in range(count - count // 2):
        c1, c2 = random.sample(code, 2)
        c3, c4 = random.sample(code, 2)
        f1 = tuple(c1[i] if i < half else c2[i] for i in range(n))
        f2 = tuple(c3[i] if i < half else c4[i] for i in range(n))
        stacks.append((f1, f2))
    return stacks


# ------------------------------------------------------------------ A, B, D
INSTANCES = [
    # (q, n, k, n_stacks, full_control)
    (5, 4, 1, 60, True),
    (7, 6, 2, 50, True),
    (11, 10, 2, 40, False),
    (17, 16, 2, 30, False),
]

a_checks = a_fail = a_sat = 0
b_checks = b_fail = 0
ctrl_checks = ctrl_fail = 0
d_band_Lge2 = 0          # Johnson-only band with L >= 2: UD bound false there
d_gap_loadbearing = 0    # stacks with L(a) > n^2 at a floor below the gap

for q, n, k, n_stacks, full_control in INSTANCES:
    code = rs_code(q, n, k)
    d = n - k + 1
    if q <= 11:
        e = max_pairwise_agreement(code, n)
        assert e == k - 1, (q, n, k, e)
    else:
        e = k - 1  # MDS: distinct deg<k polys agree on <= k-1 points
    stacks = make_stacks(code, q, n, n_stacks)
    nsq = n * n

    for f1, f2 in stacks:
        m1 = [agree_mask(g, f1, n) for g in code]
        m2 = [agree_mask(g, f2, n) for g in code]
        # exact interleaved list sizes for all floors at once
        cnt = [0] * (n + 1)
        for x in m1:
            for y in m2:
                cnt[bin(x & y).count("1")] += 1
        L = [0] * (n + 2)
        for a in range(n, -1, -1):
            L[a] = L[a + 1] + cnt[a]

        # --- A: pair-Johnson cap on every floor inside the gap
        for a in range(1, n + 1):
            gap = a * a - n * e
            if gap <= 0:
                # D: load-bearing control -- below the gap the cap formula
                # (with denominator clamped to 1) can be violated
                if L[a] > nsq:
                    d_gap_loadbearing += 1
                continue
            a_checks += 1
            if L[a] * gap > nsq:
                a_fail += 1
                ok = False
                if a_fail <= 5:
                    print(f"A FAIL q={q} n={n} a={a}: L={L[a]} "
                          f"L*gap={L[a]*gap} > n^2={nsq}")
            if L[a] * gap == nsq:
                a_sat += 1
            # Johnson-only band: gap holds but UD window fails
            if not (n + e < 2 * a) and L[a] >= 2:
                d_band_Lge2 += 1

        # --- B: composed badCount bound at collapse floors a = 2t - n
        joint_set = None
        for t in range((n + 1) // 2, n + 1):
            a = 2 * t - n
            gap = a * a - n * e
            if gap <= 0:
                continue
            LJ = nsq // gap
            # exact bad count via the witness-set reduction (exact: if some
            # S with |S|>=t works for codeword c then A_c works for c)
            bad = 0
            bad_gammas = []
            for gamma in range(q):
                line = tuple((f1[i] + gamma * f2[i]) % q for i in range(n))
                isbad = False
                for g in code:
                    cm = agree_mask(g, line, n)
                    if bin(cm).count("1") >= t:
                        cov1 = any(x & cm == cm for x in m1)
                        cov2 = any(y & cm == cm for y in m2)
                        if not (cov1 and cov2):
                            isbad = True
                            break
                if isbad:
                    bad += 1
                    bad_gammas.append(gamma)
            b_checks += 1
            rhs = 1 + (n - a) * LJ
            if bad > rhs:
                b_fail += 1
                ok = False
                if b_fail <= 5:
                    print(f"B FAIL q={q} n={n} t={t}: bad={bad} > {rhs} "
                          f"(a={a}, LJ={LJ})")

            # full 2^n subset-enumeration control on small instances
            if full_control and ctrl_checks < 400:
                if joint_set is None:
                    joint_set = sorted({x & y for x in m1 for y in m2})
                badF = 0
                for gamma in range(q):
                    line = tuple((f1[i] + gamma * f2[i]) % q
                                 for i in range(n))
                    lm = [agree_mask(g, line, n) for g in code]
                    isbad = False
                    for S in range(1 << n):
                        if bin(S).count("1") < t:
                            continue
                        if not any(cm & S == S for cm in lm):
                            continue
                        if not any(j & S == S for j in joint_set):
                            isbad = True
                            break
                    if isbad:
                        badF += 1
                ctrl_checks += 1
                if badF != bad:
                    ctrl_fail += 1
                    ok = False
                    if ctrl_fail <= 5:
                        print(f"CTRL FAIL q={q} n={n} t={t}: "
                              f"witness={bad} full={badF}")

print(f"A (pair-Johnson cap): {a_checks} (stack,floor) checks, "
      f"{a_fail} failures, saturated {a_sat}")
print(f"B (composed badCount): {b_checks} (stack,t) checks, {b_fail} failures")
print(f"CTRL (full 2^n): {ctrl_checks} controls, {ctrl_fail} mismatches")
print(f"D: Johnson-only band (gap holds, UD window fails) with L>=2: "
      f"{d_band_Lge2} cases; gap-condition load-bearing witnesses "
      f"(L > n^2 below the gap): {d_gap_loadbearing}")
if d_band_Lge2 == 0:
    print("D WARNING: the Johnson-only band never exercised L >= 2")
if d_gap_loadbearing == 0:
    print("D WARNING: no load-bearing witness for the gap condition")
    ok = False

# ------------------------------------------------------------------ C: windows
# (1-r)/3 < (1-sqrt(r))/2  <=>  sqrt(r) < (1+2r)/3  <=>  9r < (1+2r)^2
# (both sides nonneg for 0 <= r) and (1+2r)^2 - 9r = (4r-1)(r-1).
c_checks = c_fail = 0
for num in range(0, 401):
    r = Fraction(num, 400)
    lhs_lt = 9 * r < (1 + 2 * r) ** 2          # exact iff for the strict <
    expected = (4 * r - 1) * (r - 1) > 0       # polynomial sign
    claimed = r < Fraction(1, 4) or r > 1      # the named window claim
    c_checks += 1
    if lhs_lt != expected or (r <= 1 and lhs_lt != claimed):
        c_fail += 1
        ok = False
        if c_fail <= 5:
            print(f"C FAIL r={r}: 9r<(1+2r)^2={lhs_lt} "
                  f"poly={expected} claimed={claimed}")
# crossover exactly at r = 1/4: equality
r = Fraction(1, 4)
if 9 * r != (1 + 2 * r) ** 2:
    ok = False
    print("C FAIL: no equality at r = 1/4")
# numeric anchors (floats, display only) + exact comparisons
for num_r, third, half_j in [(Fraction(1, 8), None, None),
                             (Fraction(1, 16), None, None)]:
    third = (1 - num_r) / 3
    # exact: third < (1-sqrt r)/2  <=>  9r < (1+2r)^2 (checked above);
    # display floats
    print(f"C anchor rho={num_r}: (1-rho)/3={float(third):.4f}  "
          f"(1-sqrt(rho))/2={(1 - float(num_r) ** 0.5) / 2:.4f}")
# N-containment: UD window ==> Johnson gap (4ne <= (n+e)^2 < 4a^2)
cont_checks = cont_fail = 0
for n in range(1, 40):
    for e in range(0, n):
        for a in range(1, n + 1):
            if n + e < 2 * a:
                cont_checks += 1
                if not n * e < a * a:
                    cont_fail += 1
                    ok = False
if cont_fail:
    print(f"C containment FAIL: {cont_fail}/{cont_checks}")
print(f"C (window arithmetic): {c_checks} exact grid points, {c_fail} "
      f"failures; crossover at rho=1/4 exact; UD=>gap containment "
      f"{cont_checks} points, {cont_fail} failures")

# ------------------------------------------- demonstration instance, explicit
# RS(16,2)/F17: d=15, e=1.  d/(3n)=5/16=0.3125 (O84 window), formalized
# Johnson window delta < (1-sqrt(e/n))/2 = (1-1/4)/2 = 0.375.  At
# delta = 0.32 (strictly beyond d/(3n)): t = ceil(0.68*16) = 11, a = 6,
# gap 16*1 = 16 < 36 holds, UD window 17 < 12 fails.
n, e = 16, 1
delta = Fraction(32, 100)
t = ceil((1 - delta) * n)
a = 2 * t - n
in_o84 = 3 * (n - t) < n - e          # 3(n-t) < d
gap_holds = n * e < a * a
ud_holds = n + e < 2 * a
print(f"DEMO RS(16,2)/F17 delta=0.32: t={t} a={a} "
      f"O84-window={in_o84} johnson-gap={gap_holds} UD-window={ud_holds} "
      f"L_J={n*n//(a*a-n*e)}")
if in_o84 or not gap_holds or ud_holds:
    ok = False
    print("DEMO FAIL: expected outside O84+UD, inside Johnson gap")

print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
