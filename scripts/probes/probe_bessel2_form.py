from fractions import Fraction as F
from math import factorial

# besselCoeff(d,2) = sum over tuples m in (Fin d -> N) with sum = 2 of prod 1/(m_i!)^2
# tuples summing to 2: either one coord = 2 (rest 0): d such, term = 1/(2!)^2 = 1/4
#   or two distinct coords = 1 (rest 0): C(d,2) such, term = 1/(1!)^2 * 1/(1!)^2 = 1
# so besselCoeff d 2 = d * 1/4 + C(d,2)*1 = d/4 + d(d-1)/2 = (d + 2d(d-1))/4 = (2d^2 - d)/4 = d(2d-1)/4
for d in [1,2,3,4,8,16,64]:
    val = F(d,4) + F(d*(d-1),2)
    conj = F(d*(2*d-1),4)
    print("d=", d, "decomp=", val, "closed=", conj, "match=", val==conj)

# base inequality r=1: SharpNewton at r=1 is  (1+1) c_0 c_2 <= 1 * c_1^2
# = 2 * 1 * d(2d-1)/4 <= d^2  <=>  d(2d-1)/2 <= d^2  <=> d(2d-1) <= 2d^2 <=> 2d^2 - d <= 2d^2 <=> -d <= 0. TRUE.
print("base r=1 reduces to: 2*c0*c2 <= c1^2  i.e.  2d^2 - d <= 2d^2  (slack d > 0).")
