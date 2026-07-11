from fractions import Fraction as F

def c1(d): return F(d)
def c2(d): return F(d*(2*d-1),4)
def c3(d): return F(d*(6*d*d-9*d+4),36)

for d in [2,3,4,8,16,64]:
    gap = 2*c2(d)**2 - 3*c1(d)*c3(d)
    # candidate closed forms
    f1 = F(d*d*(6*d-5),72)
    print("d=", d, "gap=", gap, "d^2(6d-5)/72=", f1, "match1=", gap==f1)

# solve closed form: gap is a quartic in d. Let me fit.
# 2*(d(2d-1)/4)^2 = 2*d^2(2d-1)^2/16 = d^2(2d-1)^2/8
# 3*d*d(6d^2-9d+4)/36 = d^2(6d^2-9d+4)/12
# gap = d^2[(2d-1)^2/8 - (6d^2-9d+4)/12]
# common denom 24: d^2[3(2d-1)^2 - 2(6d^2-9d+4)]/24
# = d^2[3(4d^2-4d+1) - 12d^2+18d-8]/24 = d^2[12d^2-12d+3 -12d^2+18d-8]/24
# = d^2[6d -5]/24
for d in [2,3,4,8]:
    print("d=", d, "gap=", 2*c2(d)**2-3*c1(d)*c3(d), "d^2(6d-5)/24=", F(d*d*(6*d-5),24))
