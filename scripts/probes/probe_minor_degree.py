## Probe: does the minor polynomial drop degree below 2D for structured readout rows?
## A6deep: deg(pα·pβm − pαm·pβ) ≤ 2D. We test whether the OFFSET-ROW structure
## (pαm is the (degree-1)-offset of pα; pβm of pβ) forces a leading-coeff cancellation
## bringing deg(minor) down to ≤ D (which would discharge MinorImageLeBudget: |image|≤n).
import sympy as sp
import random

u = sp.symbols('u')

def minor_deg(pa, pam, pb, pbm):
    d = sp.expand(pa*pbm - pam*pb)
    return sp.Poly(d, u).degree() if d != 0 else -1

print("=== generic degree-D rows (expect 2D, no cancellation) ===")
for D in [2,3,4]:
    random.seed(D)
    pa = sum(random.randint(1,5)*u**i for i in range(D+1))
    pam= sum(random.randint(1,5)*u**i for i in range(D+1))
    pb = sum(random.randint(1,5)*u**i for i in range(D+1))
    pbm= sum(random.randint(1,5)*u**i for i in range(D+1))
    print("  D=%d: deg(minor)=%s (2D=%d)" % (D, minor_deg(pa,pam,pb,pbm), 2*D))

print("=== pure-monomial offset rows (rows proportional -> minor identically 0, VACUOUS) ===")
for (a,b) in [(2,3),(3,5),(4,2)]:
    print("  a=%d,b=%d: deg(minor)=%s" % (a,b, minor_deg(u**a, u**(a-1), u**b, u**(b-1))))

print("=== two-term Gauss-period-type rows h_c = u^c + const (offset shares const) ===")
for (a,b,ca,cb) in [(2,3,1,1),(3,4,2,1),(4,5,1,3),(5,7,2,2)]:
    pa, pam = u**a + ca, u**(a-1) + ca
    pb, pbm = u**b + cb, u**(b-1) + cb
    d = minor_deg(pa,pam,pb,pbm)
    print("  a=%d,b=%d: deg(minor)=%s (2D=%d, D=%d)" % (a,b,d, 2*max(a,b), max(a,b)))

print("=== full complete-homog rows h_c(u) = (u^{c+1}-1)/(u-1) truncated (geometric) ===")
## h_c = 1 + u + ... + u^c  (degree c). Offset h_{c-1} = 1+...+u^{c-1} (degree c-1).
for (a,b) in [(3,4),(4,5),(5,7),(6,8)]:
    pa  = sum(u**i for i in range(a+1))
    pam = sum(u**i for i in range(a))
    pb  = sum(u**i for i in range(b+1))
    pbm = sum(u**i for i in range(b))
    d = minor_deg(pa,pam,pb,pbm)
    print("  a=%d,b=%d: deg(minor)=%s (2D=%d, D=%d, a+b-1=%d)" % (a,b,d, 2*max(a,b), max(a,b), a+b-1))
