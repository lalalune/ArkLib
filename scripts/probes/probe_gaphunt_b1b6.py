"""
B1: at the binding radius, is the far-line incidence I(delta) controlled by M (the max), or by a WEAKER
    statistic (which would give slack = the prize easier than the wall)?
B6: is the KKH26 ceiling (r=k+1 easy direction) strictly ABOVE the worst-case floor binding (gap positive)?
Compute I(delta) = max far-line incidence directly, find binding radius, compare to M-prediction.
"""
import itertools, math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
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
def forced_count(p,n,S,k,a,b):
    ra,rb=a-k,b-k
    if ra<0 or rb<0: return None
    def hr(R,r):
        dp=[0]*(r+1);dp[0]=1
        for x in R:
            for j in range(min(r,len(dp)-1),0,-1):
                dp[j]=(dp[j]+x*dp[j-1])%p
        return dp[r]
    vals=set()
    for R in itertools.combinations(S,k+1):
        hb=hr(R,rb)
        if hb==0:continue
        vals.add((-hr(R,ra)*pow(hb,p-2,p))%p)
    return len(vals)

print("B6: ceiling (r=k+1 easy dir) vs worst-case floor binding (deepest fold where list<=budget n):")
for n in (8,16):
    p=primes1modn(n,50*n**4,1)[0]; S=subgroup(p,n); k=n//4; budget=n
    # ceiling: r=k+1 -> a=k+(k+1)=2k+1, the easy KKH26 direction; its list
    # floor: sweep all far folds, find the WORST (largest list); binding = where worst list <= budget
    print(f"  n={n} budget={budget} k={k}:")
    worst_by_fold={}
    for r in range(1, 2*k+2):
        a=k+r; b=k
        c=forced_count(p,n,S,k,a,b)
        if c is not None: worst_by_fold[r]=c
    # binding fold m* = smallest fold where list <= budget (list decreasing in deep r)
    bind=None
    for r in sorted(worst_by_fold):
        if worst_by_fold[r]<=budget: bind=r; break
    ceil_fold=k+1
    print(f"    list by fold: {dict(list(worst_by_fold.items())[:8])}")
    print(f"    KKH26 ceiling fold r=k+1={ceil_fold} (list={worst_by_fold.get(ceil_fold,'?')}); "
          f"floor binding fold m*={bind} (list={worst_by_fold.get(bind,'?') if bind else '?'})")
    print(f"    => gap (floor binds DEEPER than ceiling): {bind is not None and bind > ceil_fold}")
