import itertools
from collections import Counter

# CLAIM: a 6-tuple (ordered) over an alphabet that splits into m = n/2 antipodal CLASSES,
# each class having exactly 2 elements {+, -}, sums to zero IFF for each class the number
# of '+' entries equals the number of '-' entries (class-balanced).
# So count = #{ordered 6-tuples of (class, sign) pairs : each class balanced}.
#
# Count ordered 6-tuples: pick for each position a class c in [m] and a sign s in {+,-}.
# Balanced: for every class, #(+ in that class) = #(- in that class).
#
# Equivalent: distribute 6 positions; within each used class, equal +/-. So each class
# used contributes an EVEN number of positions (2k), with exactly k '+' and k '-'.
# Sum of (2k_c) = 6 over classes. Partitions of 6 into even parts: 6=6, 6=4+2, 6=2+2+2.
#
# For a class getting 2k positions: choose WHICH positions (later), and assign k '+'/k '-':
# C(2k, k) sign-arrangements.
#
# Let's count ordered tuples = sum over "shapes" (which classes get how many positions)
#   * multinomial(6; sizes) [assign positions to classes]
#   * product over classes C(2k_c, k_c) [sign arrangement within class]
#   * (ways to choose distinct classes from m)
#
# Partition types of 6 into even parts:
# (6):     one class with 6 positions. classes: m choices. positions: C(6,6)=1 way to pick all.
#          sign: C(6,3)=20. count = m * 1 * 20 = 20m.
# (4,2):   two DISTINCT classes, one gets 4 one gets 2. Ordered assignment of sizes to classes:
#          choose ordered pair of distinct classes (class_4, class_2): m*(m-1).
#          positions: choose 4 of 6 for class_4: C(6,4)=15, rest to class_2.
#          signs: C(4,2)*C(2,1)=6*2=12.
#          count = m*(m-1) * 15 * 12 = 180 m(m-1).
# (2,2,2): three DISTINCT classes each 2 positions. choose 3 distinct classes (unordered set
#          since all same size): C(m,3). assign positions: multinomial(6;2,2,2)=720/8=90.
#          signs per class: C(2,1)=2 each => 2^3=8.
#          count = C(m,3) * 90 * 8 = 720 * C(m,3).
#
# total = 20m + 180 m(m-1) + 720 * m(m-1)(m-2)/6
#       = 20m + 180m(m-1) + 120 m(m-1)(m-2)
# substitute m = n/2:

def closed(n):
    m = n//2
    from math import comb
    t6 = 20*m
    t42 = 180*m*(m-1)
    t222 = 120*m*(m-1)*(m-2)
    return t6+t42+t222

# Now expand in n: m=n/2
import sympy as sp
n=sp.symbols('n')
m=n/2
expr = 20*m + 180*m*(m-1) + 120*m*(m-1)*(m-2)
expr_simpl = sp.expand(expr)
print("Closed form in n:", expr_simpl)
print("Target:          ", sp.expand(15*n**3-45*n**2+40*n))
print("Match:", sp.simplify(expr_simpl - (15*n**3-45*n**2+40*n))==0)

# numeric check
for nn in [2,4,8,16,32]:
    print(f"n={nn}: combinatorial={closed(nn)}, target={15*nn**3-45*nn**2+40*nn}, match={closed(nn)==15*nn**3-45*nn**2+40*nn}")
