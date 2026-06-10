#!/usr/bin/env python3
"""probe_epsmca_interleaved_ud.py — bridge + interleaved-UD instantiation probe (#232, O78).

Checks, before formalizing, that the two MCA bad-event surfaces in the repo really
coincide, and that the O74 interleaved collapse instantiates to an unconditional
epsMCA upper bound on the unique-decoding-of-C^{interleaved 2} window.

C0 (reduction control): the "S = A_w suffices" reduction (take the witness set to be the
    FULL agreement set of a witness codeword) equals full 2^n subset enumeration of the
    mcaEvent existential.  Run exhaustively on the smallest config.
C1 (the bridge): for every stack, gamma, and delta on a rational grid,
      mcaEvent-badness  (real floor:  |S| >= (1-delta)*n,  truncated at 0)   [Errors.lean]
    == mcaBadSet-badness (nat floor:  t <= |S|, t = ceil((1-delta)*n))       [O74 file]
    computed through INDEPENDENT code paths (full subset enumeration vs reduction).
C1' (teeth control): replacing ceil by floor BREAKS the bridge (count witnesses).
C2 (instantiation): with e = max pairwise agreement among distinct codewords
    (i.e. e = n - d), whenever  n + e < 2*(2t - n):
      (a) the interleaved list at floor a = 2t - n has card <= 1 for EVERY stack;
      (b) #mcaBad(t) <= 1 + (n - a)  for every stack.
C2' (window necessity spot): just outside the window the list bound L <= 1 can fail.
C3 (delta-window arithmetic): delta < d/(4n)  ==>  n + e < 2*(2t - n) with
    t = ceil((1-delta)*n)  (the clean real-units window implies the nat window).

Exit 0 iff all checks pass.
"""

import itertools
import random
import sys
from fractions import Fraction
from math import ceil, floor

random.seed(232078)

FAIL = 0


def report(name, ok, detail=""):
    global FAIL
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}")
    if not ok:
        FAIL += 1


# ---------------------------------------------------------------- code utilities
def span(gens, p, n):
    words = set()
    k = len(gens)
    for coeffs in itertools.product(range(p), repeat=k):
        w = tuple(sum(c * g[i] for c, g in zip(coeffs, gens)) % p for i in range(n))
        words.add(w)
    return sorted(words)


def rs_code(p, n, k):
    """RS over GF(p), eval points 0..n-1, dim k."""
    words = set()
    for coeffs in itertools.product(range(p), repeat=k):
        w = tuple(sum(c * pow(x, j, p) for j, c in enumerate(coeffs)) % p for x in range(n))
        words.add(w)
    return sorted(words)


def min_dist_and_e(C, n):
    """(min distance d, max pairwise agreement e = n - d) over distinct codewords."""
    e = -1
    for g1, g2 in itertools.combinations(C, 2):
        agr = sum(1 for x in range(n) if g1[x] == g2[x])
        e = max(e, agr)
    if e < 0:  # singleton code: no distinct pair
        return n, 0
    return n - e, e


# ---------------------------------------------------------------- bad-event surfaces
def agree_mask(w, v, n):
    m = 0
    for x in range(n):
        if w[x] == v[x]:
            m |= 1 << x
    return m


def stack_masks(C, f1, f2, n):
    """Row-agreement masks M1[g1], M2[g2] for pairJointAgreesOn factorization."""
    M1 = [agree_mask(g, f1, n) for g in C]
    M2 = [agree_mask(g, f2, n) for g in C]
    return M1, M2


def pair_joint(S_mask, M1, M2):
    """pairJointAgreesOn C S f1 f2  ==  (exists g1 covering S in row 1) AND (same row 2)."""
    return any((S_mask & ~m) == 0 for m in M1) and any((S_mask & ~m) == 0 for m in M2)


def line_word(f1, f2, gamma, p, n):
    return tuple((f1[x] + gamma * f2[x]) % p for x in range(n))


def tmax(C, f1, f2, gamma, p, n, M1, M2):
    """max{|A_w| : w in C, NOT pairJoint(A_w)} (or -1): badness_nat(t) <=> t <= tmax,
    badness_real(delta) <=> (1-delta)*n <= tmax.  (The S = A_w reduction.)"""
    lw = line_word(f1, f2, gamma, p, n)
    best = -1
    for w in C:
        A = agree_mask(lw, w, n)
        if not pair_joint(A, M1, M2):
            best = max(best, bin(A).count("1"))
    return best


def bad_full_subsets(C, f1, f2, gamma, p, n, M1, M2, floor_real):
    """mcaEvent via FULL subset enumeration: exists S, |S| >= floor_real (Fraction),
    line agrees with some codeword on S, and not pairJoint(S)."""
    lw = line_word(f1, f2, gamma, p, n)
    Aw = [agree_mask(lw, w, n) for w in C]
    for S in range(1 << n):
        if Fraction(bin(S).count("1")) < floor_real:
            continue
        if not any((S & ~a) == 0 for a in Aw):
            continue
        if not pair_joint(S, M1, M2):
            return True
    return False


# ---------------------------------------------------------------- configs
P3 = 3
CODE_A = span([(1, 1, 1, 0), (0, 1, 2, 1)], 3, 4)        # F3, n=4 (the O74 witness code)
CODE_B = rs_code(3, 3, 2)                                  # F3 RS n=3 k=2
CODE_Z = [(0, 0, 0)]                                       # F3 zero code n=3
CODE_R5 = rs_code(5, 4, 2)                                 # F5 RS n=4 k=3? no: k=2, d=3

DELTAS = [Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(1, 3), Fraction(1, 2),
          Fraction(5, 8), Fraction(2, 3), Fraction(3, 4), Fraction(1), Fraction(9, 8)]


def oneminus(delta):
    return max(Fraction(0), 1 - delta)


# ---------------------------------------------------------------- C0 + C1 + C1'
def run_bridge(code, p, n, label, exhaustive, n_samples=400, do_full=True):
    """C0/C1/C1' on one code.  exhaustive: all stacks; else sampled."""
    c0_bad = c1_bad = 0
    c1p_wit = 0  # floor-instead-of-ceil mismatches (teeth)
    checked = 0
    if exhaustive:
        stacks = itertools.product(itertools.product(range(p), repeat=n), repeat=2)
    else:
        stacks = ((tuple(random.randrange(p) for _ in range(n)),
                   tuple(random.randrange(p) for _ in range(n))) for _ in range(n_samples))
    for f1, f2 in stacks:
        M1, M2 = stack_masks(code, f1, f2, n)
        for gamma in range(p):
            tm = tmax(code, f1, f2, gamma, p, n, M1, M2)
            for delta in DELTAS:
                om = oneminus(delta)
                t_ceil = ceil(om * n)
                bad_nat = (t_ceil <= tm)              # mcaBadSet surface (reduction)
                if do_full:
                    bad_real = bad_full_subsets(code, f1, f2, gamma, p, n, M1, M2, om * n)
                else:
                    bad_real = (Fraction(tm) >= om * n) if tm >= 0 else False
                checked += 1
                if bad_real != bad_nat:
                    c1_bad += 1
                # teeth: floor convention
                t_floor = floor(om * n)
                bad_floor = (t_floor <= tm)
                if bad_real != bad_floor:
                    c1p_wit += 1
                # C0: reduction == full enumeration (only when full path ran)
                if do_full:
                    bad_red = (Fraction(tm) >= om * n) if tm >= 0 else False
                    if bad_red != bad_real:
                        c0_bad += 1
    if do_full:
        report(f"C0 reduction==full-subsets [{label}]", c0_bad == 0,
               f"({checked} (stack,gamma,delta) checks, {c0_bad} mismatches)")
    report(f"C1 bridge real-floor==ceil-nat-floor [{label}]", c1_bad == 0,
           f"({checked} checks, {c1_bad} mismatches)")
    return c1p_wit, checked


tw_a, na = run_bridge(CODE_A, 3, 4, "F3 n=4 spanA, exhaustive", True)
tw_b, nb = run_bridge(CODE_B, 3, 3, "F3 n=3 RS(3,2), exhaustive", True)
tw_z, nz = run_bridge(CODE_Z, 3, 3, "F3 n=3 zero code, exhaustive", True)
tw_5, n5 = run_bridge(CODE_R5, 5, 4, "F5 n=4 RS(4,2), sampled", False, 400)
report("C1' teeth: floor-convention breaks the bridge somewhere",
       tw_a + tw_b + tw_z + tw_5 > 0,
       f"({tw_a + tw_b + tw_z + tw_5} floor-mismatch witnesses across all configs)")


# ---------------------------------------------------------------- C2 instantiation
def run_instantiation(code, p, n, label, exhaustive, n_samples=400):
    d, e = min_dist_and_e(code, n)
    windows = []
    for t in range(n + 1):
        a = max(0, 2 * t - n)
        if n + e < 2 * a:
            windows.append((t, a))
    if not windows:
        print(f"[info] C2 [{label}]: window empty (d={d}, e={e}) — skipped")
        return
    viol_list = viol_count = 0
    sat_max = -1
    checked = 0
    if exhaustive:
        stacks = list(itertools.product(itertools.product(range(p), repeat=n), repeat=2))
    else:
        stacks = [(tuple(random.randrange(p) for _ in range(n)),
                   tuple(random.randrange(p) for _ in range(n))) for _ in range(n_samples)]
    for f1, f2 in stacks:
        M1, M2 = stack_masks(code, f1, f2, n)
        tm = [tmax(code, f1, f2, g, p, n, M1, M2) for g in range(p)]
        for (t, a) in windows:
            # (a) interleaved list at floor a has card <= 1
            L = sum(1 for m1 in M1 for m2 in M2 if bin(m1 & m2).count("1") >= a)
            if L > 1:
                viol_list += 1
            # (b) bad count <= 1 + (n - a)
            bad = sum(1 for g in range(p) if t <= tm[g])
            sat_max = max(sat_max, bad - (1 + (n - a)))
            if bad > 1 + (n - a):
                viol_count += 1
            checked += 1
    report(f"C2a interleaved list card<=1 in window [{label}] d={d},e={e},windows={windows}",
           viol_list == 0, f"({checked} (stack,t) checks, {viol_list} violations)")
    report(f"C2b #mcaBad <= 1+(n-a) in window [{label}]",
           viol_count == 0, f"({checked} checks, {viol_count} violations, max slack {sat_max})")


run_instantiation(CODE_A, 3, 4, "F3 n=4 spanA, exhaustive", True)
run_instantiation(CODE_B, 3, 3, "F3 n=3 RS(3,2), exhaustive", True)
run_instantiation(CODE_R5, 5, 4, "F5 n=4 RS(4,2), sampled", False, 400)

# C2': just OUTSIDE the window the list bound can fail (necessity spot-check).
def window_necessity(code, p, n, label, exhaustive=True, n_samples=2000):
    d, e = min_dist_and_e(code, n)
    found = False
    # largest a with n + e >= 2a (outside window)
    for t in range(n, -1, -1):
        a = max(0, 2 * t - n)
        if n + e >= 2 * a and a > 0:
            if exhaustive:
                stacks = itertools.product(itertools.product(range(p), repeat=n), repeat=2)
            else:
                stacks = ((tuple(random.randrange(p) for _ in range(n)),
                           tuple(random.randrange(p) for _ in range(n)))
                          for _ in range(n_samples))
            for f1, f2 in stacks:
                M1, M2 = stack_masks(code, f1, f2, n)
                L = sum(1 for m1 in M1 for m2 in M2 if bin(m1 & m2).count("1") >= a)
                if L > 1:
                    found = True
                    break
            break
    report(f"C2' outside-window L<=1 fails somewhere [{label}]", found,
           f"(witness found at largest outside a={a})" if found else "(no witness)")


window_necessity(CODE_A, 3, 4, "F3 n=4 spanA")
window_necessity(CODE_B, 3, 3, "F3 n=3 RS(3,2)")

# ---------------------------------------------------------------- C3 delta-window
c3_bad = 0
c3_checked = 0
for (code, p, n, label) in [(CODE_A, 3, 4, "spanA"), (CODE_B, 3, 3, "RS32"),
                            (CODE_R5, 5, 4, "RS52")]:
    d, e = min_dist_and_e(code, n)
    for num in range(0, 4 * n * 4):
        delta = Fraction(num, 4 * n * 4)  # fine grid in [0,1)
        if delta >= Fraction(d, 4 * n):
            continue
        t = ceil(oneminus(delta) * n)
        a = max(0, 2 * t - n)
        c3_checked += 1
        if not (n + e < 2 * a):
            c3_bad += 1
            print(f"  C3 counterexample: {label} delta={delta} t={t} a={a} n+e={n+e}")
report("C3 delta < d/(4n) implies the nat window", c3_bad == 0,
       f"({c3_checked} grid points, {c3_bad} failures)")

print()
if FAIL:
    print(f"{FAIL} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
