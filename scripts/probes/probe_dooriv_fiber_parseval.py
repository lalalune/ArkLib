# Probe: trivial-cocycle transform is Parseval-extremal (delta), full l2 mass n^2 on one fiber.
# transform value at frequency b: T(b) = sum_{g<n} zeta^{(b+c) g}, zeta primitive n-th root, c fixed shift.
# Over b in 0..n-1 (the n frequencies), each T(b) = n if (b+c)==0 mod n else 0.
# So sum_b |T(b)|^2 = n^2, all on one frequency. Total l2 mass n^2; sup^2 = n^2.
import cmath, math
def transform(b, c, n, zeta):
    return sum(zeta**(((b+c) % n)*g) for g in range(n))
bad=0
for n in [2,4,8,16,32,64,128]:
    zeta = cmath.exp(2j*math.pi/n)
    for c in range(n):
        vals = [transform(b,c,n,zeta) for b in range(n)]
        l2 = sum(abs(v)**2 for v in vals)
        nonzero = [b for b in range(n) if abs(vals[b])>1e-6]
        sup2 = max(abs(v)**2 for v in vals)
        if abs(l2 - n*n) > 1e-4: bad+=1; print("L2 BAD n=%d c=%d l2=%.3f"%(n,c,l2))
        if len(nonzero)!=1: bad+=1; print("NOT DELTA n=%d c=%d support=%d"%(n,c,len(nonzero)))
        if abs(sup2 - n*n) > 1e-4: bad+=1; print("SUP BAD n=%d c=%d"%(n,c))
print("VERDICT:", "TRIVIAL COCYCLE IS PARSEVAL-EXTREMAL DELTA (l2=n^2 on one fiber, sup^2=n^2)" if bad==0 else "FAILED bad=%d"%bad)
