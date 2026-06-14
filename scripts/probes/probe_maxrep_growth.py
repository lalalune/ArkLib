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
def num_divisors(n):
    return sum(1 for d in range(1,n+1) if n%d==0)
# max_{t!=0} r(t) over MANY primes per n; compare to d(n) (divisor count) and constants
print(f"{'n':>4}{'#primes':>8}{'max r(t)':>10}{'d(n)':>6}{'where t s.t.':>14}")
for n in [6,12,24,36,48,60,30,42,40,56,2*3*5*7]:
    worst=0; cnt=0; worst_t=None
    for p in range(n*n+1, n*n*120):
        if not is_prime(p) or (p-1)%n: continue
        G=subgroup(p,n)
        if G is None or len(set(G))!=n: continue
        Gset=set(G)
        for t in range(1,p):
            rt=sum(1 for a in G if (t-a)%p in Gset)
            if rt>worst: worst=rt; worst_t=(p,t)
        cnt+=1
        if cnt>=12: break
    print(f"{n:>4}{cnt:>8}{worst:>10}{num_divisors(n):>6}{str(worst_t):>14}")
