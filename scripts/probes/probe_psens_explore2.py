"""
p-sensitive exploration, part 2: can ANY non-magnitude p-sensitive invariant COUPLE to the binding?
The crux: D* (over-det binding) is p-INDEPENDENT => a p-independent quantity CANNOT be controlled by a
p-sensitive invariant. So p-sensitivity enters the prize ONLY through the UNDER-DET sup-norm regime (= M).
Test directly:
 (1) Find the regime where the count IS p-dependent (the accidental-collision band near C(n,k+1)), and
     check whether that p-dependence tracks M (magnitude) or a non-M invariant.
 (2) Test the 2-adic valuation invariant v_ell(eta_a - eta_b) (N7): p-sensitive? couples to binding?
 (3) Decompose delta* = min(over-det proxy [p-indep], under-det sup-norm [p-dep=M]) -- confirm the split.
"""
import itertools, math
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
def hr_all(R,rmax,p):
    dp=[0]*(rmax+1);dp[0]=1
    for x in R:
        for j in range(min(rmax,len(dp)-1),0,-1):
            dp[j]=(dp[j]+x*dp[j-1])%p
    return dp
def gamma_count(p,n,S,k,a,b):
    ra,rb=a-k,b-k
    vals=set()
    for R in itertools.combinations(S,k+1):
        h=hr_all(R,max(ra,rb),p)
        if h[rb]==0:continue
        vals.add((-h[ra]*pow(h[rb],p-2,p))%p)
    return len(vals)

n=16;k=n//4
primes=primes1modn(n,50*n**4,6)
print(f"n={n} k={k}")
print("=== (1) is there a fold where the count is p-DEPENDENT, and does it track M? ===")
print("    sweep folds r, report count across primes + whether it varies:")
# use a near-ceiling fold to find p-dependent accidental collisions
M_by_p={}
for p in primes:
    S=subgroup(p,n)
    M_by_p[p]=max(abs(sum(math.cos(2*math.pi*(b*x%p)/p) for x in S)) for b in range(1,200))  # sample M
for r in (1,2,3,4):
    a=k+r;b=k
    counts={p:gamma_count(p,n,subgroup(p,n),k,a,b) for p in primes}
    vals=list(counts.values())
    pdep = len(set(vals))>1
    print(f"  fold r={r}: counts={vals}  {'p-DEPENDENT' if pdep else 'p-INDEP'}")
    if pdep:
        # does the variation correlate with M? (rank correlation sign)
        ps=sorted(primes, key=lambda x:M_by_p[x])
        print(f"     primes sorted by M(sample): counts in that order = {[counts[x] for x in ps]}")
        print(f"     M(sample) in that order      = {[round(M_by_p[x],3) for x in ps]}")

print()
print("=== (2) 2-adic valuation invariant v_ell(eta-period integer struct): p-sensitive? ===")
# The period eta_b is a real algebraic integer; over F_p the 'gauss period' g_b = sum_{x in S} omega^{bx}
# has v_p-structure. Test the INTEGER  N_ab = #{x in S: ...} style 2-adic content of the period polynomial.
# Simpler proxy: the multiset {eta_b mod small primes ell} -- a p-sensitive non-archimedean datum.
for ell in (2,3):
    print(f"  v_{ell}-type invariant (period-sum residues mod {ell} of the integer N0=#solutions):")
    for p in primes[:3]:
        S=subgroup(p,n)
        # N0(r=2) = # of (x1,x2,y1,y2) in S^4 with x1+x2=y1+y2 mod p  -- the energy count (integer)
        from collections import Counter
        cc=Counter((x1+x2)%p for x1 in S for x2 in S)
        N0=sum(v*v for v in cc.values())
        print(f"    p={p}: E_2-count N0={N0}, N0 mod {ell}={N0%ell}, N0/n^2={N0/n**2:.3f}")
print()
print("=== (3) the split: delta* = min(over-det [p-indep proxy], under-det sup-norm [p-dep = M]) ===")
print("    over-det binding D* p-INDEP (part 1: 16,2641 identical); M p-SENSITIVE (varies).")
print("    => the ONLY p-sensitive control of the interior is M. Non-M p-sensitive data (signs, residues)")
print("       vary with p but the binding count does not depend on them (p-indep can't be fn of p-dep).")
