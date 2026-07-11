# EXACT char-p additive energy excess of mu_n (n=2^mu) vs Wick budget.
# Tests the prize moment condition: Excess(r) = E_r - n^{2r}/q <= (2r-1)!!*n^r ?
# and the antipodal reduction (excess depends only on antisymmetric part).
from itertools import product
from math import comb
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    if p==2: return 1
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
    g0=primroot(p); g=pow(g0,(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def Er(roots,p,r):
    # f(t)=#{r-tuples summing to t}; E_r = sum f(t)^2
    f={}
    for tup in product(roots,repeat=r):
        s=sum(tup)%p
        f[s]=f.get(s,0)+1
    return sum(v*v for v in f.values())
def dblfact(m): # (2r-1)!!
    x=1
    while m>0: x*=m; m-=2
    return x
print("n  r   p       E_r        n^2r/q      Excess        Wick=(2r-1)!!n^r   Excess/Wick   verdict",flush=True)
for n in [8,16,32]:
    # huge prime ~ char-0 proxy, and a ladder of small primes p = 1 mod n
    smalls=[]
    p=n+1
    while len(smalls)<5:
        if isprime(p): smalls.append(p)
        p+=n
    # char-0 proxy: a big prime
    pbig=n+1
    while not (isprime(pbig) and pbig>10**7): pbig+=n
    for r in ([2,3,4] if n<=16 else [2,3]):
        wick=dblfact(2*r-1)*(n**r)
        # char-0 value
        rb=gmu(pbig,n); E0=Er(rb,pbig,r)
        for p in smalls+[pbig]:
            roots=gmu(p,n); E=Er(roots,p,r)
            rand=(n**(2*r))/p
            exc=E-rand
            tag="char0" if p==pbig else ""
            ratio=exc/wick if wick else 0
            ok = "OK" if exc<=wick*1.0001 else "**EXCEEDS**"
            print(f"{n:<3}{r:<3}{p:<8}{E:<11}{rand:<12.1f}{exc:<14.1f}{wick:<18}{ratio:<13.4f}{ok} {tag}",flush=True)
        # also report char-0 E0 vs Wick (is char-0 value exactly Wick-ish?)
        print(f"    -> char0 E_r={E0}  Wick(2r-1)!!n^r={wick}  E0/Wick={E0/wick:.4f}",flush=True)
