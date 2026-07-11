def isprime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x = x*x%n
            if x==n-1: break
        else:
            return False
    return True

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f

def primitive_root(p):
    if p==2: return 1
    phi=p-1
    facs=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs):
            return g
    raise RuntimeError("no prim root")

def find_primes(n, beta=4, count=3):
    target=int(round(n**beta)); out=[]
    k=target-(target%n)+1
    while len(out)<count and k<target*6:
        if k>1 and isprime(k) and (k-1)%n==0: out.append(k)
        k+=n
    return out
