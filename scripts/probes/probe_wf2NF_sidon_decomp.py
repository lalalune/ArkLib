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

# Decompose E2 in prize regime. E2 = #{(a,b,c,d): a+b=c+d in S}
# Trivial solutions: (a,b)=(c,d) -> n^2 ; (a,b)=(d,c) -> n^2 ; overlap a=b -> n
# So Sidon part = 2n^2 - n. Extra = antipodal: a+b=0 collisions since -1 in S.
# #{(a,b): a+b=0} = n (each a pairs with -a). r(0)=n -> contributes n^2 to E2 via t=0 bucket
# but trivial already counted some. Let's just measure r(t) distribution.
for n in [16,32,64]:
    p=n**4
    while not (isprime(p) and (p-1)%n==0): p+=1
    S=subgroup(p,n)
    cnt=Counter((a+b)%p for a in S for b in S)
    r0=cnt[0]  # representations of 0
    dist=Counter(cnt.values())  # how many sums have rep-count v
    E2=sum(v*v for v in cnt.values())
    # predicted: most sums have r=2 (a+b and b+a), the n sums to 0 have r=n? no
    print(f"n={n} p={p} r(0)={r0} E2={E2} 3n2-3n={3*n*n-3*n}")
    print(f"   rep-count distribution {{repcount: how_many_t}}: {dict(sorted(dist.items()))}")
    # E2 breakdown: bucket t=0 contributes r0^2; others
    others=E2-r0*r0
    print(f"   r(0)^2={r0*r0}, rest={others}, rest/(2n2-n)={others/(2*n*n-n):.4f}")
