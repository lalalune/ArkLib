import math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    for q in (3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%m==0:continue
        x=pow(a,d,m);ok=(x==1)
        for _ in range(s):
            if x==m-1:ok=True;break
            x=x*x%m
        if not ok:return False
    return True
def find_primes(n,target,count):
    out=[];p=target-(target%n)+1
    while len(out)<count and p<target*4:
        if is_prime(p):out.append(p)
        p+=n
    return out
def subgroup(p,n):
    for g0 in range(2,200):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return g0
    return None
def maxperiod(n,p):
    g0=subgroup(p,n)
    if g0 is None:return None
    H=[pow(g0,(p-1)//n*i,p) for i in range(n)]
    tp=2*math.pi;f=(p-1)//n;g=g0
    M=0.0;rep=1
    for j in range(f):
        c=0.0
        for x in H:c+=math.cos(tp*((rep*x)%p)/p)
        if abs(c)>M:M=abs(c)
        rep=(rep*g)%p
    return M
print("CREEP TEST: M/√(n ln p) at β=4, generic primes (does it plateau or grow → refute?)")
print(f"{'n':>5} {'p':>11} {'M':>7} {'M/√n':>6} {'M/√(n ln p)':>12} {'M/√(2n ln p)':>13}")
for n in [16,32,64,128]:
    target=n**4
    ps=find_primes(n,target,3)
    for p in ps[:3]:
        if p> 300_000_000: continue
        M=maxperiod(n,p)
        if M is None: continue
        lnp=math.log(p)
        print(f"{n:>5} {p:>11} {M:>7.2f} {M/math.sqrt(n):>6.2f} {M/math.sqrt(n*lnp):>12.3f} {M/math.sqrt(2*n*lnp):>13.3f}",flush=True)
