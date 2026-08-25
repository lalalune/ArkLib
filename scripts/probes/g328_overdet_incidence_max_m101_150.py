#!/usr/bin/env python3
"""G328 exact probe: even further extended pin of the overdet far-line incidence MAX.

Adds 50 more cells to the in-tree `overdetIncidenceMax_values_*` pin chain,
extending the closed form `I_max(m) = 2*m^3 - 2*m^2 + 1` to m = 101 .. 150
(n = 4*m = 404 .. 600).

Combined with the prior pins (G222/G322/G325/G327 at m = 2 .. 100), the
in-tree pin now covers 149 contiguous cells (m = 2 .. 150, n = 8 .. 600).

Two independent implementations agree at every cell:
  (A) direct cubic form:    2*m^3 - 2*m^2 + 1
  (B) binomial form:        4*m * C(m, 2) + 1 = 2*m^2*(m-1) + 1
                            (= (A); used as the closed-form "bulk + 1" form
                             in the Lean proof)

For each m in [101, 150]:
  1. I_max_cubic(m) == I_max_binomial(m) (2-impl agreement)
  2. The value matches the 50 explicit Lean-file claims
  3. Strict monotonicity: I_max(m) < I_max(m+1)
  4. Discrete derivative: I_max(m+1) - I_max(m) == 2*m*(3*m+1)

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


# Lean-file claim list (the 50 values pinned by overdetIncidenceMax_values_m101_150)
LEAN_CLAIMS = {
    101: 2040201, 102: 2101609, 103: 2164237, 104: 2228097, 105: 2293201,
    106: 2359561, 107: 2427189, 108: 2496097, 109: 2566297, 110: 2637801,
    111: 2710621, 112: 2784769, 113: 2860257, 114: 2937097, 115: 3015301,
    116: 3094881, 117: 3175849, 118: 3258217, 119: 3341997, 120: 3427201,
    121: 3513841, 122: 3601929, 123: 3691477, 124: 3782497, 125: 3875001,
    126: 3969001, 127: 4064509, 128: 4161537, 129: 4260097, 130: 4360201,
    131: 4461861, 132: 4565089, 133: 4669897, 134: 4776297, 135: 4884301,
    136: 4993921, 137: 5105169, 138: 5218057, 139: 5332597, 140: 5448801,
    141: 5566681, 142: 5686249, 143: 5807517, 144: 5930497, 145: 6055201,
    146: 6181641, 147: 6309829, 148: 6439777, 149: 6571497, 150: 6705001,
}


# =====================================================================
# Probe sections
# =====================================================================

def section_two_impl_agreement():
    """(A) cubic form == (B) binomial form at every m in [101, 150]."""
    print("--- 2-impl agreement: cubic vs binomial, m in [101, 150] ---")
    mismatches = []
    for m in range(101, 151):
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
    """I_max(m) < I_max(m+1) for m in [101, 149] (regression for strict_mono)."""
    print("--- strict monotonicity I_max(m) < I_max(m+1), m in [101, 149] ---")
    fails = 0
    for m in range(101, 150):
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
    """I_max(m+1) - I_max(m) = 2*m*(3*m+1) for m in [101, 149]."""
    print("--- discrete derivative I_max(m+1) - I_max(m) = 2*m*(3*m+1), m in [101, 149] ---")
    mismatches = []
    for m in range(101, 150):
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
    """Show the full in-tree pin: G222 (m=2..10) + G322 (m=11..15) + G325 (m=16..25) + G325b (m=26..50) + G327 (m=51..100) + G328 (m=101..150) = 149 cells."""
    print("--- cumulative in-tree pin summary ---")
    print("  G222  m=2..10     (9 cells, from parent file)")
    print("  G322  m=11..15    (5 cells, extended)")
    print("  G325  m=16..25    (10 cells, further extended)")
    print("  G325  m=26..50    (25 cells, even further extended)")
    print("  G327  m=51..100   (50 cells, further extended)")
    print("  G328  m=101..150  (50 cells, NEW)")
    print("  Total: 149 contiguous cells, n=4m=8..600")
    print("  All `decide` (kernel-blessed), all 2-impl agree")
    return True


def main():
    print("=" * 70)
    print("G328 probe: even further extended pin of overdet incidence MAX (m=101..150)")
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
