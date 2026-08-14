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

print("=== closed form c2 = d(2d-1)/4 check ===")
for d in [1,2,4,8,16,32,64,128]:
    c2 = bessel(d,2)
    conj = F(d*(2*d-1),4)
    print("d=", d, "c2=", c2, "conj=", conj, "match=", c2==conj)

print("=== SharpNewton (r+1)c_{r-1}c_{r+1} <= r c_r^2, r=1..29 ===")
for d in [2,4,8,16,64,256]:
    allok = True
    worst = None
    for r in range(1,16):
        cm = bessel(d,r-1); cr = bessel(d,r); cp = bessel(d,r+1)
        lhs = F(r+1)*cm*cp; rhs = F(r)*cr*cr
        ok = lhs <= rhs
        allok = allok and ok
        ratio = float(rhs/lhs) if lhs != 0 else 9e9
        if worst is None or ratio < worst[1]:
            worst = (r, ratio)
    print("d=", d, "all hold=", allok, "tightest(r,rhs/lhs)=", worst)

print("=== r=1 exact: 2 c2 <= c1^2 = d^2 ===")
for d in [2,4,8,16,64,1024]:
    c2 = bessel(d,2)
    print("d=", d, "2c2=", 2*c2, "d^2=", d*d, "slack=", F(d*d)-2*c2)
