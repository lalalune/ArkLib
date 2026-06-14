import cmath, math
def isprime(q):
    if q<2: return False
    for p in range(2,int(q**.5)+1):
        if q%p==0: return False
    return True
def factor(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def maxratio(n,p):
    g=primroot(p); m=(p-1)//n
    z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]   # mu_n
    mx=0.0; b=1
    for i in range(m):                                # b=g^i ranges over coset reps
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
        if v>mx: mx=v
        b=b*g%p
    return mx/math.sqrt(2*n*math.log(m))
def primes_for(n, lo, cnt):
    out=[]; q=lo
    while len(out)<cnt:
        if isprime(q) and (q-1)%n==0: out.append(q)
        q+=1
    return out
for (n, lo, cnt) in [(16, 60000, 25), (32, 1000000, 8)]:
    rs=[maxratio(n,p) for p in primes_for(n,lo,cnt)]
    print(f"n={n} beta~{math.log(lo)/math.log(n):.2f} ({len(rs)}p): max|eta|/sqrt(2n log m) min={min(rs):.3f} mean={sum(rs)/len(rs):.3f} MAX={max(rs):.3f} {'*** >1 REFUTES ***' if max(rs)>1 else 'all<1 floor holds'}",flush=True)
