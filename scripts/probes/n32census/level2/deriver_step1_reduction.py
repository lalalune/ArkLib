"""DERIVER STEP 1: verify the algebraic reduction of the consistency equation.

ORIGINAL (RESULTS-LEVEL2.md A.1):   e2(x1,x2,x3) - e1(x1,x2,x3)^2 = lam + e1(B_z)
CLAIMED REDUCTION:                  e2(x) + e1(B_z) + e1(O_z) - z* = 0   (lam = -z*)

Chain to verify:
  (a) [pure algebra]      e1(x)^2 = (x1^2+x2^2+x3^2) + 2 e2(x)
  (b) [root-of-fiber]     x_i^2 = z_{o_i}  =>  x1^2+x2^2+x3^2 = e1(O_z)
  (c) substitute:  e2 - e1^2 = e2 - e1(O_z) - 2 e2 = -e2 - e1(O_z)
      so original <=>  -e2 - e1(O_z) = lam + e1(B_z)
                  <=>  e2 + e1(B_z) + e1(O_z) + lam = 0
                  <=>  e2 + e1(B_z) + e1(O_z) - z* = 0          [lam = -z*]
Then check the ORIGINAL equation itself against 20 sample data elements (both signs).
"""
import glob
from collections import Counter

# ---------- (a) symbolic: exact multivariate polynomial arithmetic over Z ----------
# polynomials = dict {exponent-tuple over vars (x1,x2,x3,lam,e1B): int coeff}
VARS = 5  # x1 x2 x3 lam e1B


def mono(i):
    e = [0]*VARS; e[i] = 1
    return {tuple(e): 1}


def padd(*ps):
    r = Counter()
    for p in ps:
        for k, c in p.items():
            r[k] += c
    return {k: c for k, c in r.items() if c}


def pneg(p):
    return {k: -c for k, c in p.items()}


def pmul(a, b):
    r = Counter()
    for ka, ca in a.items():
        for kb, cb in b.items():
            r[tuple(x+y for x, y in zip(ka, kb))] += ca*cb
    return {k: c for k, c in r.items() if c}


X1, X2, X3, LAMs, E1Bs = (mono(i) for i in range(5))
e1 = padd(X1, X2, X3)
e2 = padd(pmul(X1, X2), pmul(X1, X3), pmul(X2, X3))
sumsq = padd(pmul(X1, X1), pmul(X2, X2), pmul(X3, X3))
# (a)  e1^2 - (sumsq + 2 e2) == 0
assert padd(pmul(e1, e1), pneg(padd(sumsq, e2, e2))) == {}
print("[a] e1^2 = sum x_i^2 + 2 e2 : IDENTITY (exact integer expansion == 0)")

# (c)  (e2 - e1^2 - lam - e1B)  ==  -(e2 + e1B + sum x_i^2 + lam)   identically
orig2 = padd(e2, pneg(pmul(e1, e1)), pneg(LAMs), pneg(E1Bs))
red = pneg(padd(e2, E1Bs, sumsq, LAMs))
assert padd(orig2, pneg(red)) == {}
print("[c] e2 - e1^2 - lam - e1B == -(e2 + e1B + sum x_i^2 + lam) : IDENTITY")
print("    => original = 0  <=>  e2 + e1(B_z) + e1(O_z) + lam = 0"
      "  <=>  e2 + e1(B_z) + e1(O_z) - z* = 0   (lam = -z*)")

# ---------- data spot check: 20 elements, original equation EXACTLY as stated ----------
P = 2013265921
g0 = 31
h32 = pow(g0, (P - 1) // 32, P)
H = [pow(h32, i, P) for i in range(32)]
G = [H[(2*z) % 32] for z in range(16)]
LAM = 284861408
ZS = pow(g0, (P - 1) // 4, P)
assert (LAM + ZS) % P == 0 and ZS == H[8]
w = [(pow(x, 18, P) + LAM * pow(x, 16, P)) % P for x in H]

def load(pat):
    out = []
    for f in sorted(glob.glob(pat)):
        for line in open(f):
            out.append(tuple(map(int, line.split())))
    return out

d17 = sorted(set(load("/tmp/n32census/audit_independent/my17_*.txt")))
assert len(d17) == 1344
import random
random.seed(232)
sample = random.sample(d17, 20)
for v in sample:
    T = [i for i in range(32) if v[i] == w[i]]
    assert len(T) == 17
    B, X, O = [], [], []
    for z in range(16):
        a, b = z in T, (z+16) in T
        if a and b: B.append(z)
        elif a: X.append(H[z]); O.append(z)
        elif b: X.append(H[z+16]); O.append(z)
    assert len(B) == 7 and len(X) == 3
    x1v, x2v, x3v = X
    e1v = (x1v + x2v + x3v) % P
    e2v = (x1v*x2v + x1v*x3v + x2v*x3v) % P
    e1Bv = sum(G[z] for z in B) % P
    e1Ov = sum(G[z] for z in O) % P
    # original, EXACT sign convention of RESULTS-LEVEL2.md:
    assert (e2v - e1v*e1v - LAM - e1Bv) % P == 0, "ORIGINAL equation fails!"
    # reduced:
    assert (e2v + e1Bv + e1Ov - ZS) % P == 0, "REDUCED equation fails!"
    # sub-identity (b):
    assert sum(x*x % P for x in X) % P == e1Ov
print("[d] 20 random data elements: ORIGINAL eq (exact RESULTS-LEVEL2 sign convention) holds,")
print("    REDUCED eq  e2 + e1(B_z) + e1(O_z) - z* = 0  holds, and sum x_i^2 = e1(O_z) holds.")
print("STEP1 DONE: reduction VERIFIED (algebra + data).")
