import cmath, math
from collections import Counter

def prime_factors(m):
    f=[]; d=2
    while d*d<=m:
        while m%d==0: f.append(d); m//=d
        d+=1
    if m>1: f.append(m)
    return f

def subgroup(p, n):
    assert (p-1) % n == 0
    g=None
    pf=set(prime_factors(p-1))
    for cand in range(2,p):
        if all(pow(cand,(p-1)//q,p)!=1 for q in pf):
            g=cand; break
    h=pow(g,(p-1)//n,p)
    S=sorted({pow(h,k,p) for k in range(n)})
    assert len(S)==n
    return S

def eta(p,S,b):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((b*x)%p)) for x in S)

def Zj(p,S,j):
    cur=[0]*p; cur[0]=1
    for _ in range(j):
        nxt=[0]*p
        for a in range(p):
            ca=cur[a]
            if ca:
                for x in S:
                    nxt[(a+x)%p]+=ca
        cur=nxt
    return cur[0]

cases=[(17,4),(97,8),(193,8),(257,16),(7681,16),(12289,16),(40961,16)]
for p,n in cases:
    if (p-1)%n: continue
    S=subgroup(p,n)
    for j in [2,3,4,5]:
        lhs=sum(eta(p,S,b)**j for b in range(p))
        z=Zj(p,S,j)
        rhs=p*z
        ok=abs(lhs.imag)<1e-5 and abs(lhs.real-rhs)<1e-4*max(1,abs(rhs))
        print(f"p={p} n={n} beta={math.log(p)/math.log(n):.2f} j={j}: Re(sum eta^j)={lhs.real:+.3f} im={lhs.imag:+.1e} p*Z_j={rhs} Z_j={z} {'OK' if ok else 'FAIL'}")
