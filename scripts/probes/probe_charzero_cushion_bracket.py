#!/usr/bin/env python3
"""#444 — char-0 cushion two-sided bracket probe (rule 2, exact integer arithmetic).

Verifies the deficit upper bound  D_r = wick_r - E_r(C)  <=  C(r,2)*(2r-1)!!*n^(r-1)  on n>=2,
the lower companion of the in-tree `deficit_r_pos` (E_r <= wick). Together they bracket the
char-0 energy ratio:   1 - C(r,2)/n  <=  E_r/wick_r  <=  1   (the K_eff -> 1-from-below cushion).

E_r closed forms are the in-tree `_CharZeroEnergyClosedForm` (r=2..6) + landed
`_AvL2_E{8,9}ClosedForm` (r=8,9) values. Run:  python probe_charzero_cushion_bracket.py
"""
from math import comb, prod

def dfact(m):  # (2r-1)!!
    r = 1
    k = m
    while k > 0:
        r *= k
        k -= 2
    return r

# in-tree exact closed forms, coeffs high->low (degree r down to 1)
E = {
 2: [3, -3, 0],
 3: [15, -45, 40, 0],
 4: [105, -630, 1435, -1155, 0],
 5: [945, -9450, 39375, -77175, 57456, 0],
 6: [10395, -155925, 1022175, -3534300, 6246471, -4370520, 0],
 8: [2027025, -56756700, 728377650, -5439183750, 25055875845, -69934975110,
     107438611995, -68492499075, 0],
 9: [34459425, -1240539300, 20744573850, -206963306550, 1327347186165,
     -5524263935190, 14357763632355, -20957471507115, 12885585512800, 0],
}

def evalpoly(coeffs, n):
    v = 0
    for c in coeffs:
        v = v * n + c
    return v

allok = True
for r in sorted(E):
    w = dfact(2 * r - 1)            # wick leading (2r-1)!!
    C = comb(r, 2)                  # second-coeff multiplier
    assert E[r][0] == w, (r, E[r][0], w)
    assert E[r][1] == -C * w, (r, E[r][1], -C * w)
    bound = C * w                   # coeff of n^(r-1) in the deficit upper bound
    ok = True
    for n in list(range(2, 60)) + [100, 1000, 2 ** 20]:
        Er = evalpoly(E[r], n)
        wick = w * n ** r
        deficit = wick - Er
        rhs = bound * n ** (r - 1)
        # both halves of the bracket
        if not (0 <= deficit <= rhs):
            ok = False
            print(f"  r={r} n={n} FAIL: 0<={deficit}<={rhs}? ")
    allok &= ok
    print(f"r={r}: wick={w} C(r,2)={C}  bracket  0 <= D_r <= {bound}*n^(r-1)  -> {'OK' if ok else 'FAIL'}")

print("\nALL CLEAN" if allok else "\nVIOLATIONS FOUND")
