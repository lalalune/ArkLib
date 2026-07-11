import math
from sympy import isprime, primitive_root
from collections import Counter

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    return S

def Er(S,p,r):
    # E_r = #{ (a_1..a_r, b_1..b_r): sum a = sum b } = sum_t (rfold(t))^2
    # rfold = r-fold sumset rep count
    cnt=Counter()
    cnt[0]=1
    for _ in range(r):
        nc=Counter()
        for t,c in cnt.items():
            for a in S:
                nc[(t+a)%p]+=c
        cnt=nc
    return sum(c*c for c in cnt.values())

# moment bound: M^{2r} <= sum_{b!=0}|eta_b|^{2r} = q*Er - n^{2r}. M <= (q*Er - n^{2r})^{1/2r}
print(f"{'n':>4} {'p':>10} {'r':>3} {'Er':>14} {'Er/(2r-1)!!n^r':>14} {'Mbound':>9} {'Mb/sqrtn':>9}")
df2=lambda r: math.prod(range(1,2*r,2))  # (2r-1)!!
for n in [16,32]:
    p=n**4
    while not (isprime(p) and (p-1)%n==0): p+=1
    S=subgroup(p,n)
    for r in [2,3,4,5,6]:
        Erv=Er(S,p,r)
        wick=df2(r)*n**r
        Mb=(p*Erv - n**(2*r))**(1.0/(2*r))
        print(f"{n:>4} {p:>10} {r:>3} {Erv:>14} {Erv/wick:>14.4f} {Mb:>9.3f} {Mb/math.sqrt(n):>9.4f}")
    print()
