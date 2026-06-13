# Energy excess of PROPER multiplicative subgroups mu_n in F_p (n << p).
# excess = E(mu_n) - (3n^2 - 3n).  Question: does excess grow ~n^2 (Sidon-ish) or larger?
# Also report |mu_n + mu_n| (sumset) to test the sum-product dichotomy.
from itertools import product
def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def subgroup(p,n):
    # generator of the order-n subgroup of F_p^*
    for g in range(2,p):
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(g,i,p) for i in range(n)]
    return None
def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def energy_excess(p,n):
    G=subgroup(p,n)
    if G is None or len(set(G))!=n: return None
    Gset=set(G)
    # additive energy E = #{(a,b,c,d): a+b=c+d} = sum_t r(t)^2, r(t)=#{(a,b): a+b=t}
    from collections import Counter
    r=Counter()
    for a in G:
        for b in G:
            r[(a+b)%p]+=1
    E=sum(v*v for v in r.values())
    excess=E-(3*n*n-3*n)
    sumset=len(r)  # |G+G|
    return E,excess,sumset
print(f"{'p':>7}{'n':>5}{'E':>9}{'3n^2-3n':>9}{'excess':>9}{'exc/n^2':>9}{'|G+G|':>7}{'n^2':>7}{'SP|G+G|/n^2':>12}")
# pick primes with a proper divisor n in a moderate range, n << p
cases=[]
for p in range(11,4000):
    if not is_prime(p): continue
    for n in prime_factors(p-1) | {d for d in range(4,int((p-1)**0.5)+2) if (p-1)%d==0}:
        if 4<=n and n*n < p and n>=6:  # proper subgroup, n << sqrt(p)-ish
            cases.append((p,n))
seen=set()
for p,n in sorted(cases, key=lambda x:(x[1],x[0])):
    if n in seen: continue  # one representative p per n (smallest p with n^2<p)
    res=energy_excess(p,n)
    if res is None: continue
    E,excess,sumset=res
    seen.add(n)
    print(f"{p:>7}{n:>5}{E:>9}{3*n*n-3*n:>9}{excess:>9}{excess/(n*n):>9.2f}{sumset:>7}{n*n:>7}{sumset/(n*n):>12.3f}")
    if len(seen)>=14: break
