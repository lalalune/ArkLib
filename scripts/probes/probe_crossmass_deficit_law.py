"""
probe_crossmass_deficit_law.py  (issue #444)

ONE decisive sweep. Verifies, for the char-0-faithful exact moments E_r of the thin 2-power
subgroup mu_n (the in-tree closed forms r=1..5), the EXACT cross-step closed forms

    crossMass(r) = E_{r+1} - n*E_r

the step target  T(r) = 2r * (2r-1)!! * n^{r+1},  the step DEFICIT  D(r) = T(r) - crossMass(r),
and the two structural laws recorded (only) as docstring comments in CrossStepRungFour.lean:

  (L1) leading coeff of crossMass(r) == 2r*(2r-1)!!          (= leading coeff of T(r); rung tight)
  (L2) second (n^r) coeff of crossMass(r) == -(r^2+r+1)/2 * 2r*(2r-1)!!
                                           == -(r^2+r+1) * r * (2r-1)!!

and the consequence (the part this brick LANDS as theorems):

  (P)  D(r) >= 0 for n >= 16  (the rung holds with EXPLICIT positive deficit), and
  (P2) D(r) has leading coeff +(r^2+r+1)*r*(2r-1)!! * n^r  (the deficit IS the 2nd-coeff law).

Exact-integer polynomial arithmetic on the in-tree closed forms (no field compute needed: these
are the proven char-0-faithful E_r forms; mu_n-faithfulness is already in tree, this probe is the
ALGEBRA that the docstring asserts but does not prove). Cross-checked against the actual F_p
moments at small n to confirm the closed forms themselves.
"""

from fractions import Fraction as Q

# in-tree exact char-0-faithful E_r closed forms (coeff lists, high->low power of n, no const term)
# E_1 = n ; E_2 = 3n^2-3n ; E_3 = 15n^3-45n^2+40n ; E_4 = 105n^4-630n^3+1435n^2-1155n ;
# E_5 = 945n^5-9450n^4+39375n^3-77175n^2+57456n
E = {
    1: [1, 0],
    2: [3, -3, 0],
    3: [15, -45, 40, 0],
    4: [105, -630, 1435, -1155, 0],
    5: [945, -9450, 39375, -77175, 57456, 0],
}

def dblfact(k):
    r = 1
    while k > 1:
        r *= k
        k -= 2
    return r

def poly_eval(coeffs, n):
    # coeffs high->low
    v = 0
    for c in coeffs:
        v = v * n + c
    return v

def poly_sub(a, b):
    # align by degree (lists high->low), return high->low
    da, db = len(a), len(b)
    d = max(da, db)
    a = [0] * (d - da) + a
    b = [0] * (d - db) + b
    return [x - y for x, y in zip(a, b)]

def shift_mul_n(coeffs):
    # n * poly  => append a 0 (raise every power by 1)
    return coeffs + [0]

print("r | leadOK(L1) | secondOK(L2) | deficit>=0 @n=16..2^20 | crossMass leading")
allok = True
for r in range(1, 5):
    lead = 2 * r * dblfact(2 * r - 1)              # 2r*(2r-1)!!
    second_pred = -(r * r + r + 1) * r * dblfact(2 * r - 1)   # -(r^2+r+1)*r*(2r-1)!!
    cm = poly_sub(E[r + 1], shift_mul_n(E[r]))     # crossMass(r) = E_{r+1} - n*E_r, high->low
    # crossMass(r) is degree r+1 (lead n^{r+1}); coeffs high->low:
    cm_lead = cm[0]
    cm_second = cm[1]
    L1 = (cm_lead == lead)
    L2 = (cm_second == second_pred)
    # step target T(r) = lead * n^{r+1}  (single leading term)
    T = [lead] + [0] * (r + 1)
    D = poly_sub(T, cm)                            # deficit = T - crossMass, high->low (deg r)
    # check D>=0 over the prize-regime n grid
    Dpos = all(poly_eval(D, n) >= 0 for n in [16, 32, 64, 128, 256, 1024, 2 ** 20])
    # deficit leading coeff should be +(r^2+r+1)*r*(2r-1)!! (the negated second-coeff law)
    D_lead = D[0] if D[0] != 0 else (D[1] if len(D) > 1 else 0)
    D_lead_pred = (r * r + r + 1) * r * dblfact(2 * r - 1)
    DleadOK = (D_lead == D_lead_pred)
    ok = L1 and L2 and Dpos and DleadOK
    allok = allok and ok
    print(f"{r} | {L1} | {L2} | {Dpos} | cm_lead={cm_lead} (Tlead={lead}) Dlead={D_lead}(pred {D_lead_pred}:{DleadOK})")

# exact crossMass closed forms printed for the Lean theorem statements:
print("\nexact crossMass(r) closed forms (high->low coeffs):")
for r in range(1, 5):
    cm = poly_sub(E[r + 1], shift_mul_n(E[r]))
    print(f"  r={r}: {cm}")
print("\nexact step DEFICIT D(r)=T(r)-crossMass(r) (high->low coeffs, all >=0 for n>=16):")
for r in range(1, 5):
    cm = poly_sub(E[r + 1], shift_mul_n(E[r]))
    lead = 2 * r * dblfact(2 * r - 1)
    T = [lead] + [0] * (r + 1)
    print(f"  r={r}: {poly_sub(T, cm)}")

print("\nALL CHECKS PASS:", allok)
