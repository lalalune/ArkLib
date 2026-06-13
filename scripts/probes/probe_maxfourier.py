import cmath, math
def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def subgroup(p,n):
    for g in range(2,p):
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(g,i,p) for i in range(n)]
    return None
# max_{xi!=0} |S(xi)|^2 where S(xi)=sum_{a in mu_n} e_p(xi*a).  Is it O(n) or ~p?
print(f"{'p':>6}{'n':>4}{'n^2/p':>7}{'max|S|^2':>10}{'/n':>7}{'/sqrt(p)':>9}{'E':>8}{'E/n^2':>7}")
for (n,) in [(6,),(8,),(10,),(12,),(16,),(20,),(24,),(30,)]:
    # pick p with n^2<p (deployed), smallest such
    for p in range(n*n+1, n*n*30):
        if not is_prime(p) or (p-1)%n: continue
        G=subgroup(p,n)
        if G is None or len(set(G))!=n: continue
        # max over xi
        maxS2=0
        for xi in range(1,p):
            S=sum(cmath.exp(2j*math.pi*xi*a/p) for a in G)
            maxS2=max(maxS2, abs(S)**2)
        from collections import Counter
        r=Counter()
        for a in G:
            for b in G: r[(a+b)%p]+=1
        E=sum(v*v for v in r.values())
        print(f"{p:>6}{n:>4}{n*n/p:>7.2f}{maxS2:>10.1f}{maxS2/n:>7.2f}{maxS2/math.sqrt(p):>9.2f}{E:>8}{E/(n*n):>7.2f}")
        break
