# Probe: the concrete class-balanced count B(k,m) and its add-one-class recursion (rec2/rec4/rec6).
# B(k,m) = #{ c : Fin k -> (Fin m x Bool) : for every class j, #{i: c i=(j,true)} = #{i: c i=(j,false)} }
# i.e. tuples of length k over m antipodal classes {z,-z}, each class used with equal +/- multiplicity.
# This is the zero-sum count E_{k/2}(mu_{2m}) under the Lam-Leung balance characterization.
from itertools import product

def B_brute(k, m):
    if m == 0:
        return 1 if k == 0 else 0
    cnt = 0
    for c in product(range(m * 2), repeat=k):  # each entry: class*2 + sign (sign in {0,1})
        ok = True
        for j in range(m):
            plus = sum(1 for x in c if x == j * 2 + 1)
            minus = sum(1 for x in c if x == j * 2 + 0)
            if plus != minus:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt

def B2cf(m): return 2 * m
def B4cf(m): return 12 * m**2 - 6 * m
def B6cf(m): return 120 * m**3 - 180 * m**2 + 80 * m

print("=== concrete brute B(k,m) vs closed forms ===")
for m in range(0, 4):
    b2, b4 = B_brute(2, m), B_brute(4, m)
    b6 = B_brute(6, m) if m <= 2 else None
    s6 = f"B6={b6}(cf {B6cf(m)})" if b6 is not None else "B6=skip"
    print(f"m={m}: B2={b2}(cf {B2cf(m)}) B4={b4}(cf {B4cf(m)}) {s6}")

print("=== recursion check: rec2/rec4/rec6 (add-one-class) ===")
for m in range(0, 3):
    b2m, b4m, b6m = B_brute(2, m), B_brute(4, m), B_brute(6, m)
    b2m1, b4m1, b6m1 = B_brute(2, m + 1), B_brute(4, m + 1), B_brute(6, m + 1)
    r2 = (b2m1 == b2m + 2)
    r4 = (b4m1 == b4m + 12 * b2m + 6)
    r6 = (b6m1 == b6m + 30 * b4m + 90 * b2m + 20)
    print(f"m={m}: rec2 {r2}  rec4 {r4}  rec6 {r6}")
    print(f"      b2:{b2m}->{b2m1}  b4:{b4m}->{b4m1}  b6:{b6m}->{b6m1}")
