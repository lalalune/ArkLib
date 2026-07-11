# Probe a CLEAN inductive structure for B(k,m) that is Lean-tractable.
# Idea: B(k,m) = sum over how the k positions split across m classes, each class balanced.
# Define single-class generating count a(t) = #{ length-t tuples over ONE class {+,-} that are balanced }
#   = C(t, t/2) if t even else 0.
# Then B(k,m) = sum over compositions (t_1,...,t_m) of k of  prod_i a(t_i) * (multinomial C(k; t_1..t_m)).
# Equivalently B(., m) is the m-fold "exponential convolution" of a(.).
# The add-one-class recursion is exactly: B(k,m+1) = sum_{t} C(k,t) a(t) B(k-t, m),
#   and since a(t)=0 for odd t, t=2j, a(2j)=C(2j,j):
#   B(k,m+1) = sum_j C(k,2j) C(2j,j) B(k-2j, m).
from math import comb
from itertools import product

def a(t):
    return comb(t, t // 2) if t % 2 == 0 else 0

def B_conv(k, m):
    # m-fold convolution via the recursion
    if m == 0:
        return 1 if k == 0 else 0
    total = 0
    for j in range(0, k // 2 + 1):
        total += comb(k, 2 * j) * comb(2 * j, j) * B_conv(k - 2 * j, m - 1)
    return total

def B_brute(k, m):
    if m == 0:
        return 1 if k == 0 else 0
    cnt = 0
    for c in product(range(m * 2), repeat=k):
        ok = True
        for jc in range(m):
            plus = sum(1 for x in c if x == jc * 2 + 1)
            minus = sum(1 for x in c if x == jc * 2 + 0)
            if plus != minus:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt

print("=== B_conv vs B_brute (validates the convolution recursion = the concrete count) ===")
for m in range(0, 4):
    for k in [0, 2, 4, 6]:
        bc = B_conv(k, m)
        bb = B_brute(k, m) if (m <= 2 or k <= 4) else "skip"
        match = "OK" if (bb == "skip" or bc == bb) else "MISMATCH"
        print(f"m={m} k={k}: conv={bc} brute={bb} {match}")
