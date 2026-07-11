# DECISIVE (clean): among PROPER, THIN subgroup primes (p >= n^3, index m=(p-1)/n large), does the
# char-p Wick bound E_r^{(p)} <= (2r-1)!!*n^r EVER fail, at any depth r? Exclude full-group (m=1) and
# thick (beta<3) degenerate cases. If never fails across many thin primes & all r -> CLOSURE CANDIDATE.
import cmath, math, sympy
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def Er(n,p,r):
    A=[abs(sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in musub(n,p))) for b in range(p)]
    return sum(a**(2*r) for a in A)/p
def dfact(r):
    v=1
    for i in range(1,2*r,2): v*=i
    return v
print("Thin proper primes (p>=n^3, beta>=3), scan E_r vs Wick at r=2..10. Report ANY failure + max ratio.")
for n in [8,16]:
    print(f"\n n={n} (n^3={n**3}, n^4={n**4}):")
    # collect ~10 thin primes p>=n^3, p=1 mod n
    primes=[]; m=max(2,(n**3)//n)
    while len(primes)<10:
        p=n*m+1; m+=1
        if sympy.isprime(p) and p>=n**3: primes.append(p)
    worst=0; worstinfo=None; anyfail=False
    for p in primes:
        beta=math.log(p)/math.log(n)
        for r in range(2,11):
            W=dfact(r)*n**r; e=Er(n,p,r); ratio=e/W
            if ratio>worst: worst=ratio; worstinfo=(p,beta,r,ratio)
            if e>W: anyfail=True; print(f"   FAIL p={p}(beta{beta:.1f}) r={r}: E/W={ratio:.2f}")
    print(f"   primes tested: {primes[0]}..{primes[-1]} (beta {math.log(primes[0])/math.log(n):.1f}-{math.log(primes[-1])/math.log(n):.1f})")
    print(f"   {'NO FAILURE - bound holds all r, all thin primes' if not anyfail else 'FAILS (see above)'}; worst E/W={worst:.3f} at p={worstinfo[0]} r={worstinfo[2]}")
