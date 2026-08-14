"""
Final p-sensitive stress test: does the INTERIOR-controlling object depend on more than M?
The bad-scalar count goes via the FULL spectrum (moments Sum|eta_b|^{2r}). Test:
 (A) near-max multiplicity #{b: |eta_b| > theta} across primes -- p-sensitive (Class B)?
 (B) the low MOMENTS Sum|eta_b|^{2r} across primes -- p-independent (Class C aggregate)?
 (C) the N7 2-adic invariant: valuations of period DIFFERENCES -- p-sensitive but decoupled?
If individual values + multiplicities are p-sensitive (Class B) but the moments (the thing the bad-count
needs) are p-independent until deep r (where char-p excess = Class A = wall), the picture is complete:
the full-spectrum route IS the moment method = capped by the meta-theorem = the wall.
"""
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primes1modn(n,lo,cnt):
    out=[];p=lo+(n-lo%n)+1
    while len(out)<cnt:
        if p%n==1 and isprime(p):out.append(p)
        p+=n
    return out
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def all_periods(p,n,S):
    """exact integer moments need all (p-1)/n coset values; for n=16, (p-1)/n ~ 200k -- compute via
    eta over a transversal of cosets. eta_b real. Return the list of distinct nonzero period values."""
    # coset reps: b ranges over a transversal of F_p^* / mu_n
    reps=[]; seen=set()
    # use b = generator powers stepping by n... simpler: b=1..(p-1)//n won't hit all cosets. Use:
    # every coset has a rep; iterate b and canonicalize.
    g=2
    while pow(g,(p-1)//2,p)==1: g+=1  # primitive root
    # cosets indexed by b = g^j, j=0..(p-1)/n-1 (since mu_n = <g^{(p-1)/n}>)
    m=(p-1)//n
    etas=[]
    for j in range(m):
        b=pow(g,j,p)
        etas.append(sum(math.cos(2*math.pi*(b*x%p)/p) for x in S))
    return etas

n=16;k=n//4
primes=primes1modn(n,50*n**4,5)
print(f"n={n}; m=(p-1)/n cosets each prime")
print(f"{'p':>9} {'M':>8} {'#|eta|>0.9M':>11} {'#|eta|>sqrt(n log)':>18} {'E_2/p-ish moment':>17} {'E_3 moment':>13}")
data=[]
sqrtnl=math.sqrt(n*math.log((primes[0])/n))
for p in primes:
    S=subgroup(p,n)
    et=all_periods(p,n,S)
    aet=[abs(e) for e in et]
    M=max(aet)
    mult90=sum(1 for a in aet if a>0.9*M)
    multsq=sum(1 for a in aet if a>sqrtnl)
    # moments (normalized): mean of |eta|^{2r} over cosets  ~ E_r-ish (the full-spectrum aggregate)
    mom2=sum(a**4 for a in aet)/len(aet)   # 2nd moment of |eta|^2 = 4th of |eta|
    mom3=sum(a**6 for a in aet)/len(aet)
    data.append((p,M,mult90,multsq,mom2,mom3))
    print(f"{p:>9} {M:>8.3f} {mult90:>11} {multsq:>18} {mom2:>17.1f} {mom3:>13.1f}")
print()
def pclass(vals, tol):
    return 'p-INDEP' if (max(vals)-min(vals)) <= tol*abs(sum(vals)/len(vals)) else 'p-SENSITIVE'
print("ANALYSIS:")
print(f"  M (max):            {pclass([d[1] for d in data],0.005)}  range {min(d[1] for d in data):.3f}..{max(d[1] for d in data):.3f}")
print(f"  near-max mult(>0.9M): {pclass([d[2] for d in data],0.02)}  values {[d[2] for d in data]}  (Class B candidate)")
print(f"  mult(>sqrt(n log m)): {pclass([d[3] for d in data],0.02)}  values {[d[3] for d in data]}")
print(f"  4th-moment aggregate: {pclass([d[4] for d in data],0.01)}  range {min(d[4] for d in data):.1f}..{max(d[4] for d in data):.1f}")
print(f"  6th-moment aggregate: {pclass([d[5] for d in data],0.01)}  range {min(d[5] for d in data):.1f}..{max(d[5] for d in data):.1f}")
print()
print("INTERPRETATION:")
print("  If near-max MULTIPLICITY is p-SENSITIVE (Class B) but the low MOMENTS are p-INDEPENDENT (Class C),")
print("  then the bad-count's controlling aggregate (the moment/energy) is p-indep until deep r where the")
print("  char-p excess W_r (Class A=wall) enters. The full-spectrum route = the moment method = meta-theorem")
print("  capped. No Class-B coupling to the prize survives.")
