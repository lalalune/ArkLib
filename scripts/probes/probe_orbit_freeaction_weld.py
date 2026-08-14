import itertools, math
from math import gcd
def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def find_prime(n, lo):
    p=lo-(lo%n)+1
    while True:
        if p>lo and p%n==1 and is_prime(p): return p
        p+=n
def primroot(p):
    phi=p-1; m=phi; f=[]; d=2
    while d*d<=m:
        if m%d==0:
            f.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: f.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in f): return g
def mu_n(p,n,g):
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    return S,h
def agree_ge(D,vals,k,p,t):
    Dl=list(D)
    if k>len(Dl): return len(Dl)>=t
    inv={}
    for sub in itertools.combinations(Dl,k):
        ag=0
        for x in Dl:
            num=0
            for xi in sub:
                term=vals[xi]
                for xj in sub:
                    if xj==xi: continue
                    term=term*((x-xj)%p)%p
                    key=(xi-xj)%p
                    if key not in inv: inv[key]=pow(key,p-2,p)
                    term=term*inv[key]%p
                num=(num+term)%p
            if num==vals[x]: ag+=1
        if ag>=t: return True
    return False
n=8; k=2; p=find_prime(n,150); g=primroot(p)
D,w=mu_n(p,n,g); Dset=set(D)
tJ=int(round(math.sqrt(k*n))); t=tJ+1
print("n,p,k,tJ,t=",n,p,k,tJ,t,"w=",w)
for (a,b) in [(n-6,4),(n-2,1)]:
    d=gcd(abs(b-a),n); S=n//d; mult=pow(w,(b-a)%n,p)
    B=[al for al in range(p) if agree_ge(Dset,{x:(pow(x,a,p)+al*pow(x,b,p))%p for x in D},k,p,t)]
    Bset=set(B); Bstar=[x for x in B if x!=0]; seen=set(); sizes=[]
    for a0 in sorted(Bstar):
        if a0 in seen: continue
        orb=[]; x=a0
        while x not in seen:
            seen.add(x); orb.append(x); x=x*mult%p
        sizes.append(len(orb))
    allS=all(s==S for s in sizes); match=(len(sizes)*S==len(Bstar)) and allS
    print(f"(a,b)=({a},{b}) gcd={d} S={S} |B|={len(B)} |B*|={len(Bstar)} #orb={len(sizes)} orb*S={len(sizes)*S} match={match} z={1 if 0 in Bset else 0} sizes={sizes[:8]}")

print("\n--- sweep t down to find nonempty bad sets and check orbit partition ---")
for (a,b) in [(n-6,4),(n-2,1)]:
    d=gcd(abs(b-a),n); S=n//d; mult=pow(w,(b-a)%n,p)
    for t in range(tJ+1, 1, -1):
        B=[al for al in range(p) if agree_ge(Dset,{x:(pow(x,a,p)+al*pow(x,b,p))%p for x in D},k,p,t)]
        if not B: continue
        Bset=set(B); Bstar=[x for x in B if x!=0]; seen=set(); sizes=[]
        for a0 in sorted(Bstar):
            if a0 in seen: continue
            orb=[]; x=a0
            while x not in seen:
                seen.add(x); orb.append(x); x=x*mult%p
            sizes.append(len(orb))
        allS=all(s==S for s in sizes); match=(len(sizes)*S==len(Bstar)) and allS
        print(f"(a,b)=({a},{b}) t={t} gcd={d} S={S} |B|={len(B)} |B*|={len(Bstar)} #orb={len(sizes)} match={match} z={1 if 0 in Bset else 0} sizes={sorted(set(sizes))}")
        break
