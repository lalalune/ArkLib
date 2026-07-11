# Test the ACTUAL prize moment condition Excess(r) <= (2r-1)!!*n^r at r = round(ln p)
# (the prize couples r=ln q). Convolution DP: E_r = sum_t f_r[t]^2, f = r-fold conv of mu_n.
import math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def gmu(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def Er(roots,p,r):
    f=[0]*p
    for x in roots: f[x]+=1
    for _ in range(r-1):
        nf=[0]*p
        for t in range(p):
            ft=f[t]
            if ft:
                for x in roots:
                    nf[(t+x)%p]+=ft
        f=nf
    return sum(v*v for v in f)
def dblfact(m):
    x=1
    while m>0: x*=m; m-=2
    return x
for n in [16,32]:
    print(f"\n=== n={n}: Excess(r)/Wick at r=round(ln p), prime ladder ===",flush=True)
    worst=0; worstp=0; nbad=0; tot=0
    p=n+1
    while p < 6000:
        if isprime(p):
            r=max(2,round(math.log(p)))
            roots=gmu(p,n)
            E=Er(roots,p,r)
            rand=(n**(2*r))/p
            exc=E-rand
            wick=dblfact(2*r-1)*(n**r)
            ratio=exc/wick
            tot+=1
            if ratio>1.0: nbad+=1
            if ratio>worst: worst=ratio; worstp=p
            flag="  <-- BAD (exc>Wick)" if ratio>1.0 else ""
            if ratio>0.85 or p<300:
                print(f"  p={p:<6} r={r}  Excess/Wick={ratio:.4f}{flag}",flush=True)
        p+=n
    print(f"  >>> n={n}: {nbad}/{tot} primes BAD at r=ln p; WORST={worst:.4f} at p={worstp}",flush=True)
