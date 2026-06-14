# Study the structure of the ladder to find a closed form.
# Published: r=3..8 -> 97,145,89,113,225,104. r=3 proven = n*C(n/4,2)+1.
# Look for closed forms term-by-term against n=16 (n/2=8, n/4=4).
import math
n=16
lad={3:97,4:145,5:89,6:113,7:225,8:104}
# Known r=3: n*C(n/4,2)+1 = 16*6+1=97. The "+1" = the all-real/zero config.
# Try to express each as a*C(.,.)+b combos. Print candidate building blocks:
print("Building blocks for n=16: n=16, n/2=8, n/4=4, n/8=2")
for r in range(3,9):
    print(f"r={r}: #bad={lad[r]}  K=2^{r}*C(8,{r})={2**r*math.comb(8,r)}")
print()
# The K-side count = 2^r C(n/2,r) = antipodal-free r-subsets of mu_n (KKH26). #bad ~ K / margin.
# margins: 4.62,7.72,20.1,15.9,4.55,2.46. Non-monotone => divisor-dependent (x^{n/2} vs x^{n/4} family).
# Hypothesis: #bad(r) = (contribution from x^{n/2}-line family) + (from x^{n/4} family) - overlap + 1.
# r=3 dominated by x^{n/2} (degenerate at r=4). Let me just see parities: even r are 145,113,104; odd 97,89,225.
# Try #bad = 2^r C(n/4, floor(r/2)) C(n/4, ceil(r/2)) /something ... compute symmetric splits:
g=4 # n/4
for r in range(3,9):
    # split r into two halves landing in the two order-4 cosets under x->x^2
    parts=[]
    for i in range(0,r+1):
        parts.append(math.comb(g,i)*math.comb(g, r-i) if r-i>=0 and r-i<=g and i<=g else 0)
    print(f"r={r}: sum_i C(4,i)C(4,r-i) = {sum(parts)}   parts={parts}   #bad={lad[r]}")
