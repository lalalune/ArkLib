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
# max_{t!=0} r(t) where r(t)=#{a in mu_n: t-a in mu_n}.  Is it a bounded CONSTANT?
print(f"{'p':>6}{'n':>4}{'n^2/p':>7}{'max_{t!=0} r(t)':>16}{'r(0)':>6}")
maxover=0; maxcase=None
for n in [6,8,10,12,14,16,18,20,24,30,36,40]:
    # smallest few proper primes, take worst max over them
    cnt=0; worst=0
    for p in range(n*n+1, n*n*60):
        if not is_prime(p) or (p-1)%n: continue
        G=subgroup(p,n)
        if G is None or len(set(G))!=n: continue
        Gset=set(G)
        mx=0
        for t in range(1,p):
            rt=sum(1 for a in G if (t-a)%p in Gset)
            mx=max(mx,rt)
        worst=max(worst,mx)
        cnt+=1
        if cnt>=5: break
    if worst>maxover: maxover=worst; maxcase=(n,)
    print(f"{'~':>6}{n:>4}{'':>7}{worst:>16}{n:>6}")
print(f"\nGLOBAL max_{{t!=0}} r(t) over all tested = {maxover}")
print("=> if bounded small constant: GVRepBound with CONSTANT M, E=O(n^2), provable")
