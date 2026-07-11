# Is mu_{2^mu} special (smaller max period) vs a non-2-power subgroup of same size at same p?
import cmath, math
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    for p in range(3,int(q**.5)+1,2):
        if q%p==0: return False
    return True
def fac(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def maxratio(n,p):
    g=primroot(p); m=(p-1)//n; z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]
    mx=0.0;b=1
    for i in range(m):
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
        if v>mx:mx=v
        b=b*g%p
    return mx/math.sqrt(2*n*math.log(m))
# compare n=16 (2-power) vs n=12,15,20,24 (non-2-power) at primes p with all | p-1
import itertools
for target in [200000, 2000000]:
    L=lcm=240  # lcm of 12,15,16,20,24
    q=target - (target % L) + 1
    while not isprime(q): q+=L
    p=q
    row=[]
    for n in [12,15,16,20,24]:
        if (p-1)%n==0:
            row.append((n, '2pow' if (n&(n-1))==0 else 'gen', round(maxratio(n,p),3), round(n/math.sqrt(p),3)))
    print(f"p={p} beta(n=16)={math.log(p)/math.log(16):.2f}: (n,type,max/floor,n/sqrt p) {row}",flush=True)
