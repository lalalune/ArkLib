"""Machine countermodels for the true-escape archetypes (#444).
(i) SHALLOW-BIND: does O(c) collapse to <=2 at SHALLOW c, or grow? -> if it GROWS, shallow-bind FALSE.
(ii) RIGIDITY/antipodal-worst: is the worst far-direction antipodal (list 2), or a spread word with bigger list?
Exact in F_p, p = 1 mod n, p > n^4."""
import itertools
def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
def prime1modn(n,lo):
    p=lo+(n-lo%n)+1
    while p%n!=1 or not isprime(p): p+=1
    return p
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        S=[pow(h,i,p) for i in range(n)]
        if len(set(S))==n: return S
def agreement_far(S,p,a,b,k):
    """far direction (x^a, x^b): bad scalar gamma where x^a + gamma x^b agrees with deg<k poly on >= ... 
    we measure the LIST: # distinct codewords (deg<k) within the far-line incidence = # distinct gamma giving
    >=k+1 agreements. Proxy: count distinct gamma = -P(x)/x^b-ish. Use the forced-gamma over (k+1)-subsets."""
    n=len(S)
    # h_r via complete homog on (k+1)-subsets; gamma_R = -h_{a-k}(R)/h_{b-k}(R)
    ra, rb = a-k, b-k
    if ra<0 or rb<0: return None
    def hr(R, r):
        dp=[0]*(r+1); dp[0]=1
        for x in R:
            for j in range(min(r,len(dp)-1),0,-1):
                dp[j]=(dp[j]+x*dp[j-1])%p
        return dp[r]
    vals=set()
    for R in itertools.combinations(S, k+1):
        hb=hr(R,rb)
        if hb==0: continue
        g=(-hr(R,ra)*pow(hb,p-2,p))%p
        vals.add(g)
    return len(vals)

print("=== (i) SHALLOW-BIND test: does the over-det list collapse shallow or grow with fold? ===")
print("rho=1/4, k=n/4; far direction (a,b)=(k+r, k) [fold r], list = #distinct forced-gamma:")
for n in (8,16):
    p=prime1modn(n,50*n**4); S=subgroup(p,n); k=n//4
    print(f" n={n} p={p} k={k}:")
    for r in range(1,7):
        a=k+r; b=k
        L=agreement_far(S,p,a,b,k)
        print(f"   fold r={r} (dir x^{a}+g x^{b}): list={L}")
print()
print("=== (ii) ANTIPODAL-WORST test: list at antipodal (a,b)=(n/2+k, k) vs a SPREAD/gapped direction ===")
for n in (16,):
    p=prime1modn(n,50*n**4); S=subgroup(p,n); k=n//4
    # antipodal-ish: numerator fold = n/2
    anti=agreement_far(S,p,k+n//2,k,k)
    # spread: fold = n/4 (gapped)
    spread=agreement_far(S,p,k+n//4,k,k)
    # small fold
    sm=agreement_far(S,p,k+2,k,k)
    print(f" n={n}: list(fold n/2={n//2})={anti}  list(fold n/4={n//4})={spread}  list(fold 2)={sm}")
    print("   -> if a non-antipodal fold gives a LARGER list than fold-2, the worst is NOT the shallow/antipodal one")
