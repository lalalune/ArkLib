#!/usr/bin/env python3
"""
Combinatorial closed-form proof sketch for r=3, order-2 line.

From r3_derivation: S={i1..i4} aligned with gamma  <=>  exists line W=A+Bx through
the 4 points P_i = (x_i, W_i), W_i = (-1)^i (1 + gamma x_i^{-1}).

Rewrite. Let eps_i=(-1)^i. The 4 points collinear:
  the 4x3 matrix [1, x_i, W_i] has rank <= 2.  Plug W_i = eps_i + gamma eps_i / x_i:
  columns: [1], [x_i], [eps_i + gamma eps_i/x_i].
  rank<=2 of [1, x_i, eps_i + gamma eps_i/x_i] for the 4 rows
  <=> the vector (eps_i + gamma eps_i/x_i)_i is in span{ (1)_i, (x_i)_i } over the 4 rows.
  i.e. exists A,B: eps_i (1 + gamma/x_i) = A + B x_i   for all 4 i.            (*)

Multiply by x_i:  eps_i (x_i + gamma) = A x_i + B x_i^2.
=> B x_i^2 + (A - eps_i) x_i - eps_i gamma = 0   for each i in S.               (**)

Split S by parity. For EVEN i (eps_i=+1):  B x^2 + (A-1) x - gamma = 0.
For ODD i (eps_i=-1):  B x^2 + (A+1) x + gamma = 0.
Each is a quadratic in x with <=2 roots. So among the 4 nodes' x-values:
 - even-parity nodes are roots of  Q+(x)=B x^2+(A-1)x-gamma,
 - odd-parity nodes are roots of   Q-(x)=B x^2+(A+1)x+gamma.
Each quadratic has at most 2 roots among {x_i}. So an aligned 4-set has
  (#even nodes <=2) and (#odd nodes <=2)  => the only way to place 4 nodes is
  EITHER 2 even + 2 odd, OR (degenerate B=0 linear) cases.

CASE 2-even + 2-odd (generic, B!=0):
  even nodes {a,b}: roots of Q+ => by Vieta on Q+:  a+b = -(A-1)/B,  a*b = -gamma/B.
  odd nodes {c,d}:  roots of Q- => c+d = -(A+1)/B,  c*d = gamma/B.
  Subtract sums: (a+b)-(c+d) = -(A-1)/B + (A+1)/B = 2/B.   (free A,B,gamma; 3 unknowns)
  Products:  ab = -gamma/B,  cd = gamma/B  => ab = -cd  => ab + cd = 0.            (RIGIDITY)
  So a 2-even+2-odd set {a,b | c,d} is aligned  <=>  ab + cd = 0  (x_a x_b + x_c x_d = 0),
  i.e. x_a x_b = - x_c x_d.  With x_i=g^i:  g^{a+b} = -g^{c+d} = g^{c+d+n/2}
  => a+b == c+d + n/2  (mod n).                                                   (***)
  And then gamma = -B*ab, with B = 2/((a+b)-(c+d)) in x-units... gamma = -ab*B and the
  bad scalar value (Vieta) = -(x_a+x_b+x_c+x_d) = -e1.

So: ALIGNED 2+2 sets <=> two even-indexed nodes a<b, two odd-indexed c<d with
    g^{a+b} + g^{c+d} = 0  (antipodal pair-product condition).
  The bad scalar gamma = -(g^a+g^b+g^c+g^d).

COUNT distinct gamma = #distinct values of -(g^a+g^b+g^c+g^d) over such configs, PLUS
the degenerate (collinear/B=0) families that give gamma=0.

This script enumerates the 2+2 antipodal-product configs directly (NO 4-subset loop over
all C(n,4); just the structured set) and counts distinct gamma -> verifies = n*C(n/4,2)+1
and exposes the closed-form combinatorics.
"""
import sys
from math import comb
from itertools import combinations

p = 2013265921

def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1:
            return [pow(h,i,p) for i in range(n)]

def count(n):
    dom=mu_n(n)
    evens=[i for i in range(n) if i%2==0]
    odds=[i for i in range(n) if i%2==1]
    bad=set()
    cfg=0
    for a,b in combinations(evens,2):
        for c,d in combinations(odds,2):
            # condition g^{a+b} + g^{c+d} = 0  <=>  (a+b) - (c+d) == n/2 (mod n)
            if (a+b - c - d) % n == n//2 % n or (c+d - a - b) % n == n//2 % n:
                cfg+=1
                gam=(-(dom[a]+dom[b]+dom[c]+dom[d]))%p
                bad.add(gam)
    cf=n*comb(n//4,2)+1
    print(f"n={n}: 2+2 antipodal-product configs={cfg}  distinct gamma(incl 0)={len(bad)}  0 present? {0 in bad}  closed form n*C(n/4,2)+1={cf}  match? {len(bad)==cf}")
    # also count just nonzero
    nz=len(bad - {0})
    print(f"     nonzero gamma = {nz}   n*C(n/4,2) = {n*comb(n//4,2)}   match? {nz==n*comb(n//4,2)}")

if __name__=="__main__":
    for n in [int(x) for x in (sys.argv[1:] or [16,32,64])]:
        count(n)
