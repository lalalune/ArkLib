# Probe: rigidity of the trivial-cocycle Fourier fiber.
# Claim: for r an n-th root of unity, |sum_{g<n} r^g| = n  <=>  r = 1.
# (delta-fiber converse / full-concentration rigidity)
import cmath, math
def fiber(r, n):
    return sum(r**g for g in range(n))
bad=0; tot=0
for n in [2,4,8,16,32,64,128,256]:
    for j in range(n):
        r = cmath.exp(2j*math.pi*j/n)   # r^n = 1
        s = fiber(r,n)
        tot+=1
        is_full = abs(abs(s)-n) < 1e-6
        should = (j==0)
        if is_full != should:
            bad+=1; print("MISMATCH n=%d j=%d |s|=%.4f"%(n,j,abs(s)))
        if j!=0 and abs(s)>1e-6:
            bad+=1; print("OFFSUPPORT NONZERO n=%d j=%d s=%s"%(n,j,s))
print("checked %d roots, mismatches=%d"%(tot,bad))
print("VERDICT:", "RIGIDITY HOLDS (full mass n <=> r=1)" if bad==0 else "FAILED")
