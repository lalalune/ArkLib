## Verify the EXACT minor identity for complete-homogeneous (geometric) readout rows.
## Claim: with g_c(u) := sum_{i=0}^{c} u^i = (u^{c+1}-1)/(u-1),
##   g_a * g_{b-1} - g_{a-1} * g_b  =  u^a * g_{b-a-1}   (for b > a >= 1),
## where g_{b-a-1} = sum_{i=0}^{b-a-1} u^i.  deg = a + (b-a-1) = b-1.
## This is the sharp degree = D-1 (D=max(a,b)=b), HALVING the A6deep 2D bound and landing
## BELOW the prize budget n (=> would discharge MinorImageLeBudget for a fixed direction).
import sympy as sp
u = sp.symbols('u')

def g(c):
    return sum(u**i for i in range(c+1)) if c >= 0 else 0

print("=== exact identity g_a g_{b-1} - g_{a-1} g_b = u^a g_{b-a-1} (b>a>=1) ===")
allok = True
for a in range(1, 9):
    for b in range(a+1, 12):
        lhs = sp.expand(g(a)*g(b-1) - g(a-1)*g(b))
        rhs = sp.expand(u**a * g(b-a-1))
        ok = sp.expand(lhs - rhs) == 0
        allok &= ok
        if not ok:
            print("  FAIL a=%d b=%d: lhs=%s rhs=%s" % (a,b,lhs,rhs))
print("  identity holds for all 1<=a<b<=11:", allok)

print("=== symmetric/skew check: a>b gives -u^b g_{a-b-1} (antisymmetry in a<->b) ===")
allok2 = True
for a in range(2, 10):
    for b in range(1, a):
        lhs = sp.expand(g(a)*g(b-1) - g(a-1)*g(b))
        rhs = sp.expand(-u**b * g(a-b-1))
        ok = sp.expand(lhs-rhs) == 0
        allok2 &= ok
        if not ok: print("  FAIL a=%d b=%d" % (a,b))
print("  antisymmetric form holds for all 1<=b<a<=9:", allok2)

print("=== degree of minor = b-1 = max(a,b)-1 (sharp, < D, well below 2D) ===")
for (a,b) in [(3,8),(4,16),(5,32),(7,64)]:
    minor = sp.expand(u**a * g(b-a-1))
    print("  a=%d b=%d: deg=%d  (D=%d, 2D=%d, budget-n-relevant: deg<D)" %
          (a,b, sp.Poly(minor,u).degree(), b, 2*b))
