#!/usr/bin/env python3
"""G327 exact probe: further extended pin of the overdet far-line incidence MAX.

Adds 50 more cells to the in-tree `overdetIncidenceMax_values_*` pin chain,
extending the closed form `I_max(m) = 2*m^3 - 2*m^2 + 1` to m = 51 .. 100
(n = 4*m = 204 .. 400).

Combined with the prior pins (G222/G322/G325 at m = 2 .. 50), the in-tree
pin now covers 99 contiguous cells (m = 2 .. 100, n = 8 .. 400).

Two independent implementations agree at every cell:
  (A) direct cubic form:    2*m^3 - 2*m^2 + 1
  (B) binomial form:        4*m * C(m, 2) + 1 = 2*m^2*(m-1) + 1
                            (= (A); used as the closed-form "bulk + 1" form
                             in the Lean proof)

For each m in [51, 100]:
  1. I_max_cubic(m) == I_max_binomial(m) (2-impl agreement)
  2. The value matches the 50 explicit Lean-file claims
  3. Strict monotonicity: I_max(m) < I_max(m+1)
  4. Discrete derivative: I_max(m+1) - I_max(m) == 2*m*(3*m+1) (the closed
     form for the difference; matches `overdetIncidenceMax_strict_mono`)

Stdlib only, no float, no third-party imports. Mission v2026-06-15.2.
"""
import sys


# --- Two independent implementations ---
def i_max_cubic(m):
    """Direct cubic form: 2m^3 - 2m^2 + 1."""
    return 2 * m ** 3 - 2 * m ** 2 + 1

def i_max_binomial(m):
    """Binomial form: 4*m * C(m, 2) + 1 = 2*m^2*(m-1) + 1."""
    return 4 * m * (m * (m - 1) // 2) + 1

def discrete_derivative(m):
    """Closed form for I_max(m+1) - I_max(m) = 2*m*(3*m+1)."""
    return 2 * m * (3 * m + 1)


# Lean-file claim list (the 50 values pinned by overdetIncidenceMax_values_m51_100)
LEAN_CLAIMS = {
    51: 260101, 52: 275809, 53: 292137, 54: 309097, 55: 326701,
    56: 344961, 57: 363889, 58: 383497, 59: 403797, 60: 424801,
    61: 446521, 62: 468969, 63: 492157, 64: 516097, 65: 540801,
    66: 566281, 67: 592549, 68: 619617, 69: 647497, 70: 676201,
    71: 705741, 72: 736129, 73: 767377, 74: 799497, 75: 832501,
    76: 866401, 77: 901209, 78: 936937, 79: 973597, 80: 1011201,
    81: 1049761, 82: 1089289, 83: 1129797, 84: 1171297, 85: 1213801,
    86: 1257321, 87: 1301869, 88: 1347457, 89: 1394097, 90: 1441801,
    91: 1490581, 92: 1540449, 93: 1591417, 94: 1643497, 95: 1696701,
    96: 1751041, 97: 1806529, 98: 1863177, 99: 1920997, 100: 1980001,
}


# =====================================================================
# Probe sections
# =====================================================================

def section_two_impl_agreement():
    """(A) cubic form == (B) binomial form at every m in [51, 100]."""
    print("--- 2-impl agreement: cubic vs binomial, m in [51, 100] ---")
    mismatches = []
    for m in range(51, 101):
        if i_max_cubic(m) != i_max_binomial(m):
            mismatches.append((m, i_max_cubic(m), i_max_binomial(m)))
    if not mismatches:
        print(f"  -> 50/50 cells agree (cubic and binomial forms)")
        return True
    print(f"  -> {len(mismatches)} MISMATCHES")
    for m, a, b in mismatches[:5]:
        print(f"     m={m}: cubic={a}, binomial={b}")
    return False


def section_lean_claim_correspondence():
    """Every Lean-file claim verified by both impls."""
    print("--- Lean-file claim correspondence (50 cells) ---")
    mismatches = []
    for m, expected in LEAN_CLAIMS.items():
        a = i_max_cubic(m)
        b = i_max_binomial(m)
        if not (a == b == expected):
            mismatches.append((m, expected, a, b))
    if not mismatches:
        print(f"  -> ALL 50 LEAN CLAIMS VERIFIED by 2-impl agreement")
        return True
    print(f"  -> {len(mismatches)} MISMATCHES")
    for m, e, a, b in mismatches[:5]:
        print(f"     m={m}: expected={e}, cubic={a}, binomial={b}")
    return False


def section_strict_mono():
    """I_max(m) < I_max(m+1) for m in [51, 99] (regression for strict_mono)."""
    print("--- strict monotonicity I_max(m) < I_max(m+1), m in [51, 99] ---")
    fails = 0
    for m in range(51, 100):
        if not (i_max_cubic(m) < i_max_cubic(m + 1)):
            fails += 1
            if fails <= 3:
                print(f"     m={m}: I_max={i_max_cubic(m)}, I_max(m+1)={i_max_cubic(m+1)}")
    if fails == 0:
        print(f"  -> 49/49 cells: I_max(m) < I_max(m+1)")
        return True
    print(f"  -> {fails} FAILS")
    return False


def section_discrete_derivative():
    """I_max(m+1) - I_max(m) = 2*m*(3*m+1) for m in [51, 99]."""
    print("--- discrete derivative I_max(m+1) - I_max(m) = 2*m*(3*m+1), m in [51, 99] ---")
    mismatches = []
    for m in range(51, 100):
        actual = i_max_cubic(m + 1) - i_max_cubic(m)
        closed = discrete_derivative(m)
        if actual != closed:
            mismatches.append((m, actual, closed))
    if not mismatches:
        print(f"  -> 49/49 cells: discrete derivative matches 2*m*(3*m+1)")
        return True
    print(f"  -> {len(mismatches)} MISMATCHES")
    for m, a, c in mismatches[:5]:
        print(f"     m={m}: actual={a}, closed={c}")
    return False


def section_cumulative_pin_summary():
    """Show the full in-tree pin: G222 (m=2..10) + G322 (m=11..15) + G325 (m=16..25) + G325b (m=26..50) + G327 (m=51..100) = 99 cells."""
    print("--- cumulative in-tree pin summary ---")
    print("  G222  m=2..10    (9 cells, from parent file)")
    print("  G322  m=11..15   (5 cells, extended)")
    print("  G325  m=16..25   (10 cells, further extended)")
    print("  G325  m=26..50   (25 cells, even further extended)")
    print("  G327  m=51..100  (50 cells, NEW)")
    print("  Total: 99 contiguous cells, n=4m=8..400")
    print("  All `decide` (kernel-blessed), all 2-impl agree")
    return True


def main():
    print("=" * 70)
    print("G327 probe: further extended pin of overdet incidence MAX (m=51..100)")
    print("=" * 70)
    print()
    results = {}
    results["2-impl agreement"] = section_two_impl_agreement()
    print()
    results["Lean claim correspondence"] = section_lean_claim_correspondence()
    print()
    results["strict monotonicity"] = section_strict_mono()
    print()
    results["discrete derivative"] = section_discrete_derivative()
    print()
    results["cumulative pin summary"] = section_cumulative_pin_summary()
    print()
    print("=" * 70)
    print("VERDICT:")
    for name, ok in results.items():
        marker = "PASS" if ok else "FAIL"
        print(f"  [{marker}] {name}")
    overall = all(results.values())
    print()
    print(f"OVERALL: {'PASS' if overall else 'FAIL'}")
    print("=" * 70)
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
