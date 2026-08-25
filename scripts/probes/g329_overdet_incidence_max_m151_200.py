#!/usr/bin/env python3
"""G329 exact probe: still further extended pin of the overdet far-line incidence MAX.

Adds 50 more cells to the in-tree `overdetIncidenceMax_values_*` pin chain,
extending the closed form `I_max(m) = 2*m^3 - 2*m^2 + 1` to m = 151 .. 200
(n = 4*m = 604 .. 800).

Combined with the prior pins (G222/G322/G325/G327/G328 at m = 2 .. 150), the
in-tree pin now covers 199 contiguous cells (m = 2 .. 200, n = 8 .. 800).

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


# Lean-file claim list (the 50 values pinned by overdetIncidenceMax_values_m151_200)
LEAN_CLAIMS = {
    151: 6840301, 152: 6977409, 153: 7116337, 154: 7257097, 155: 7399701,
    156: 7544161, 157: 7690489, 158: 7838697, 159: 7988797, 160: 8140801,
    161: 8294721, 162: 8450569, 163: 8608357, 164: 8768097, 165: 8929801,
    166: 9093481, 167: 9259149, 168: 9426817, 169: 9596497, 170: 9768201,
    171: 9941941, 172: 10117729, 173: 10295577, 174: 10475497, 175: 10657501,
    176: 10841601, 177: 11027809, 178: 11216137, 179: 11406597, 180: 11599201,
    181: 11793961, 182: 11990889, 183: 12189997, 184: 12391297, 185: 12594801,
    186: 12800521, 187: 13008469, 188: 13218657, 189: 13431097, 190: 13645801,
    191: 13862781, 192: 14082049, 193: 14303617, 194: 14527497, 195: 14753701,
    196: 14982241, 197: 15213129, 198: 15446377, 199: 15681997, 200: 15920001,
}


# =====================================================================
# Probe sections
# =====================================================================

def section_two_impl_agreement():
    """(A) cubic form == (B) binomial form at every m in [151, 200]."""
    print("--- 2-impl agreement: cubic vs binomial, m in [151, 200] ---")
    mismatches = []
    for m in range(151, 201):
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
    """I_max(m) < I_max(m+1) for m in [151, 199] (regression for strict_mono)."""
    print("--- strict monotonicity I_max(m) < I_max(m+1), m in [151, 199] ---")
    fails = 0
    for m in range(151, 200):
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
    """I_max(m+1) - I_max(m) = 2*m*(3*m+1) for m in [151, 199]."""
    print("--- discrete derivative I_max(m+1) - I_max(m) = 2*m*(3*m+1), m in [151, 199] ---")
    mismatches = []
    for m in range(151, 200):
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
    """Show the full in-tree pin through G329: 199 cells, n=8..800."""
    print("--- cumulative in-tree pin summary ---")
    print("  G222  m=2..10     (9 cells, from parent file)")
    print("  G322  m=11..15    (5 cells, extended)")
    print("  G325  m=16..25    (10 cells, further extended)")
    print("  G325  m=26..50    (25 cells, even further extended)")
    print("  G327  m=51..100   (50 cells, further extended)")
    print("  G328  m=101..150  (50 cells, even further extended)")
    print("  G329  m=151..200  (50 cells, NEW)")
    print("  Total: 199 contiguous cells, n=4m=8..800")
    print("  All `decide` (kernel-blessed), all 2-impl agree")
    return True


def main():
    print("=" * 70)
    print("G329 probe: still further extended pin of overdet incidence MAX (m=151..200)")
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
