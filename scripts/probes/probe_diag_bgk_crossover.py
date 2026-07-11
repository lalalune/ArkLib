import math
# Diagonal energy bound E_r <= n^{2r-1}. BGK/Wick bound E_r <= (2r-1)!! * n^r.
# Diagonal is WEAKER (larger) than BGK iff n^{2r-1} > (2r-1)!! * n^r  iff  n^{r-1} > (2r-1)!!.
# Find crossover r0(n) = least r with n^{r-1} > (2r-1)!!  (for r>=1).
# Below r0: diagonal is at-least-as-good (n^{r-1} <= (2r-1)!!) -> BGK input not yet needed.
# At/above r0: BGK strictly sharper -> the BGK (open) input is what MATTERS.
def dfact_odd(r):
    p = 1
    for i in range(r):
        p *= (2*i+1)
    return p

print("crossover r0(n) = least r>=1 with n^{r-1} > (2r-1)!!  (diagonal becomes strictly weaker than BGK)")
print("%8s %6s %s" % ("n", "r0", "(check: n^{r0-1} vs (2r0-1)!! and at r0-1)"))
for a in [2,3,4,6,8,12,16,20,24,30]:
    n = 2**a
    r0 = None
    for r in range(1, 4000):
        if n**(r-1) > dfact_odd(r):
            r0 = r
            break
    # sanity: at r0-1 the inequality should FAIL (n^{r0-2} <= (2r0-3)!!) when r0>=2
    ok_below = True
    if r0 and r0 >= 2:
        ok_below = (n**(r0-2) <= dfact_odd(r0-1))
    print("%8d %6s   below-fails=%s   (n=2^%d)" % (n, r0, ok_below, a))

print()
print("Hypothesis: r0(n) ~ ? Let's see r0 vs log2(n) and vs n.")
for a in [4,8,12,16,20,24,30]:
    n=2**a
    r0=None
    for r in range(1,8000):
        if n**(r-1) > dfact_odd(r):
            r0=r; break
    print("  n=2^%-2d  r0=%-5s  r0/a=%.3f  log2(dfact ratio at r0)~ n^{r0-1}/(2r0-1)!! = %.2e" %
          (a, r0, (r0/a if r0 else 0), n**(r0-1)/dfact_odd(r0) if r0 else 0))
