from fractions import Fraction as F
from math import factorial

def bessel(d, r):
    g = [F(1, factorial(k)**2) for k in range(r+1)]
    res = [F(0)]*(r+1)
    res[0] = F(1)
    for _ in range(d):
        new = [F(0)]*(r+1)
        for a in range(r+1):
            if res[a] == 0:
                continue
            for b in range(r+1-a):
                new[a+b] += res[a]*g[b]
        res = new
    return res[r]

# besselCoeff d 3 closed form conjecture: tuples summing to 3 over Fin d:
#  one coord = 3 (rest 0): d of them, term 1/(3!)^2 = 1/36
#  one coord = 2 + one coord = 1: d*(d-1) ordered pairs, term 1/(2!)^2 * 1/(1!)^2 = 1/4
#  three coords = 1: C(d,3), term 1
# => c3 = d/36 + d(d-1)/4 + C(d,3)
print("=== besselCoeff d 3 closed form ===")
for d in [1,2,3,4,8,16,64]:
    c3 = bessel(d,3)
    conj = F(d,36) + F(d*(d-1),4) + F(d*(d-1)*(d-2),6)
    print("d=", d, "c3=", c3, "conj=", conj, "match=", c3==conj)

# simplify conj: common denom 36: d + 9 d(d-1) + 6 d(d-1)(d-2) all /36
# = d[1 + 9(d-1) + 6(d-1)(d-2)]/36 = d[1 + 9d-9 + 6(d^2-3d+2)]/36
# = d[6d^2 -18d+12 +9d -8]/36 = d[6d^2 -9d +4]/36
print("=== simplified c3 = d(6d^2-9d+4)/36 ===")
for d in [1,2,4,8,64]:
    print("d=", d, "c3=", bessel(d,3), "simp=", F(d*(6*d*d-9*d+4),36))

# SharpNewton at r=2: (2+1) c_1 c_3 <= 2 c_2^2  i.e. 3*d*c3 <= 2*(d(2d-1)/4)^2
print("=== SharpNewton r=2: 3 c1 c3 <= 2 c2^2 ===")
for d in [2,4,8,16,64,256]:
    c1=bessel(d,1); c2=bessel(d,2); c3=bessel(d,3)
    lhs=3*c1*c3; rhs=2*c2*c2
    print("d=", d, "lhs=", lhs, "rhs=", rhs, "holds=", lhs<=rhs, "slack=", rhs-lhs)
