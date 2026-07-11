#!/usr/bin/env python3
"""
ADVERSARIAL AUDIT of the load-bearing linear_combination identities in UnitCircleSidonQuint.lean.
The Lean kernel already accepts them; this is an independent numeric cross-check that the IDENTITIES
ARE WHAT THEY CLAIM (catches a mis-stated theorem the kernel would happily prove but that wouldn't
mean what the docstring says). Random complex (NOT roots of unity — these are pure ring identities,
must hold for ALL complex a,b,c,d,e).
"""
import random, cmath
random.seed(20260617)

def rc():
    return complex(random.uniform(-3,3), random.uniform(-3,3))

def esymm5(a,b,c,d,e):
    e1 = a+b+c+d+e
    e2 = (a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e)
    e3 = (a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e)
    e4 = (a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e)
    e5 = a*b*c*d*e
    return e1,e2,e3,e4,e5

maxerr_key = 0.0
maxerr_l1 = 0.0   # leftover e1
maxerr_l2 = 0.0   # leftover e2
maxerr_l3 = 0.0   # leftover e3
for _ in range(200000):
    a,b,c,d,e = rc(),rc(),rc(),rc(),rc()
    ap,bp,cp,dp,ep = rc(),rc(),rc(),rc(),rc()
    e1,e2,e3,e4,e5 = esymm5(a,b,c,d,e)
    f1,f2,f3,f4,f5 = esymm5(ap,bp,cp,dp,ep)
    # KEY identity: (a-ap)(a-bp)(a-cp)(a-dp)(a-ep)
    #   == a^4*(e1-f1) - a^3*(e2-f2) + a^2*(e3-f3) - a*(e4-f4) + (e5-f5)  ... when e_i = f_i it's 0,
    #   but the linear_combination claims the PRODUCT equals that combination of the (h_i: e_i=f_i)
    #   residuals. Test the underlying polynomial identity directly:
    lhs = (a-ap)*(a-bp)*(a-cp)*(a-dp)*(a-ep)
    rhs = (a**4)*(e1-f1) - (a**3)*(e2-f2) + (a**2)*(e3-f3) - a*(e4-f4) + (e5-f5)
    maxerr_key = max(maxerr_key, abs(lhs-rhs))

    # leftover-quad extraction with a=w (set ap=a so a=w branch). Use {b,c,d,e} vs {bp,cp,dp,ep}
    # given quintuple esymm of (a,b,c,d,e) vs (a,bp,cp,dp,ep) all equal -> leftover identities.
    # Build the matched case: w=a, and require quintuple esymm equal.
    # leftover e1 of {b,c,d,e}:  (b+c+d+e) = (e1 - a)  and (bp+cp+dp+ep) = (f1' - a) where f1' uses a
    # We test the algebraic extraction identities (h2 - a*hs etc.) as ring identities:
    le1 = b+c+d+e
    le2 = b*c+b*d+b*e+c*d+c*e+d*e
    le3 = b*c*d+b*c*e+b*d*e+c*d*e
    le4 = b*c*d*e
    # h1 = e1 ; e1 - a = le1
    maxerr_l1 = max(maxerr_l1, abs((e1 - a) - le1))
    # h2 - a*le1 == le2   (e2 = a*le1 + le2)
    maxerr_l2 = max(maxerr_l2, abs((e2 - a*le1) - le2))
    # h3 - a*le2 == le3   (e3 = a*le2 + le3)
    maxerr_l3 = max(maxerr_l3, abs((e3 - a*le2) - le3))

print(f"KEY product identity        maxerr = {maxerr_key:.2e}  (expect ~0, ring identity)")
print(f"leftover e1 (e1 - a = le1)  maxerr = {maxerr_l1:.2e}")
print(f"leftover e2 (e2 - a*le1)    maxerr = {maxerr_l2:.2e}")
print(f"leftover e3 (e3 - a*le2)    maxerr = {maxerr_l3:.2e}")
print("All ~0 => the linear_combination identities are correctly stated (consistent w/ kernel accept).")
