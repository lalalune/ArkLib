import math
def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
def primroot(p):
    for a in range(2,p):
        x=1;seen=set();ok=True
        for _ in range(p-1):
            x=x*a%p
            if x in seen: ok=False;break
            seen.add(x)
        if ok and len(seen)==p-1: return a
def E2(p,n):
    g0=primroot(p); g=pow(g0,(p-1)//n,p); dom=[pow(g,i,p) for i in range(n)]
    # E2 = #{(a,b,c,d): a+b=c+d} = sum_s r(s)^2 where r(s)=#{(a,b): a+b=s}
    from collections import Counter
    r=Counter()
    for a in dom:
        for b in dom:
            r[(a+b)%p]+=1
    return sum(v*v for v in r.values())
print("E2(mu_n) vs random; excess = E2/(2n^2-n) (diagonal); random off-diag ~ n^4/p",flush=True)
print(f"{'p':>7} {'n':>4} {'m':>4} {'E2':>8} {'2n^2-n':>8} {'n^4/p':>8} {'rand=diag+offdiag':>17} {'E2/rand':>8}",flush=True)
for (n,m) in [(8,8),(16,8),(32,8),(64,8),(16,16),(32,16),(64,16),(32,4),(64,4),(128,4)]:
    p=m*n+1
    while not isprime(p): p+=n
    if p>20000: continue
    mm=(p-1)//n
    e=E2(p,n)
    diag=2*n*n-n
    offdiag=n**4/p  # crude random off-diagonal
    rand=diag+offdiag
    print(f"{p:>7} {n:>4} {mm:>4} {e:>8} {diag:>8} {offdiag:>8.0f} {rand:>17.0f} {e/rand:>8.2f}",flush=True)
