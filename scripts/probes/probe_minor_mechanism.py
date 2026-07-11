## Pin the EXACT mechanism of the degree drop in Δ = pα·pβm − pαm·pβ.
## Hypothesis: when the offset rows satisfy a "shift" relation lead(pα)=lead(pαm) at the
## matched top degree (the divided-difference consecutive-complete-homog structure), the
## top-degree term of pα·pβm cancels that of pαm·pβ, dropping deg by >=1 below 2D.
import sympy as sp
u = sp.symbols('u')

def lead(p):
    P = sp.Poly(sp.expand(p), u)
    return P.degree(), P.LC()

def report(name, pa, pam, pb, pbm):
    d = sp.expand(pa*pbm - pam*pb)
    dd = sp.Poly(d,u).degree() if d!=0 else -1
    da,la = lead(pa); dam,lam = lead(pam); db,lb = lead(pb); dbm,lbm = lead(pbm)
    print("%s: deg pa=%d(LC%s) pam=%d(LC%s) pb=%d(LC%s) pbm=%d(LC%s) -> deg(minor)=%s"
          % (name, da,la, dam,lam, db,lb, dbm,lbm, dd))

## Case A: complete-homog h_c = sum_{i<=c} u^i. Key: deg h_c = c, deg h_{c-1}=c-1, BOTH LC=1.
## minor top term: u^a * u^{b-1} (from pa*pbm) has deg a+b-1; pam*pb top: u^{a-1}*u^b deg a+b-1.
## Both coeff 1 -> CANCEL. So deg(minor) <= a+b-2. With a,b ~ D this is ~2D-2, NOT <= D.
## But probe showed deg ~ D-1. So a SECOND cancellation cascade happens. Investigate:
print("=== complete-homog: trace the full cancellation cascade ===")
for (a,b) in [(3,4),(4,6),(5,8)]:
    pa  = sum(u**i for i in range(a+1)); pam = sum(u**i for i in range(a))
    pb  = sum(u**i for i in range(b+1)); pbm = sum(u**i for i in range(b))
    # h_c = (u^{c+1}-1)/(u-1). minor = [(u^{a+1}-1)(u^b-1) - (u^a-1)(u^{b+1}-1)]/(u-1)^2
    num = sp.expand((u**(a+1)-1)*(u**b-1) - (u**a-1)*(u**(b+1)-1))
    minor = sp.cancel(num/(u-1)**2)
    print("  a=%d b=%d: minor=%s deg=%d (max(a,b)=%d)" %
          (a,b, sp.factor(minor), sp.Poly(sp.expand(minor),u).degree(), max(a,b)))

## closed form: num = (u^{a+1}-1)(u^b-1)-(u^a-1)(u^{b+1}-1)
##  = u^{a+1+b} - u^{a+1} - u^b + 1 - [u^{a+b+1} - u^a - u^{b+1} + 1]
##  = -u^{a+1} - u^b + u^a + u^{b+1} = u^a(1-u) + u^b(u-1) = (u-1)(u^b - u^a)
## so minor = (u-1)(u^b-u^a)/(u-1)^2 = (u^b - u^a)/(u-1) = u^a(u^{b-a}-1)/(u-1)
##          = u^a * (1 + u + ... + u^{b-a-1})  [for b>a]  -> deg = a + (b-a-1) = b-1 = D-1. CONFIRMED.
print("=== closed form check: minor = u^a*(u^{b-a}-1)/(u-1), deg = b-1 = max-1 ===")
for (a,b) in [(3,4),(4,6),(5,8),(2,7)]:
    cf = sp.expand(u**a * (u**(b-a)-1)/(u-1)) if b>a else 0
    print("  a=%d b=%d: closed-form deg=%d (b-1=%d)" % (a,b, sp.Poly(cf,u).degree() if cf!=0 else -1, b-1))
