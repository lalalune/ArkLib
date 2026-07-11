import numpy as np
from math import log, sqrt
def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for cand in range(2,p):
        h=pow(cand,e,p)
        if h==1 or pow(h,n//2,p)==1: continue
        S=set(); x=1
        for _ in range(n): x=(x*h)%p; S.add(x)
        if len(S)==n: return np.array(sorted(S))
    return None
def Mval(p,n):
    S=subgroup(p,n)
    if S is None: return None
    b=np.arange(p); eta=np.zeros(p,dtype=complex); ang=2j*np.pi/p
    for x in S: eta+=np.exp(ang*((b*x)%p))
    return sqrt((np.abs(eta[1:])**2).max())
# targeted: structured primes (p-1 = 2^v * small odd) + matched n near n/sqrt(p) in [0.2,0.6]
results=[]
for a in range(3,8):          # n=8..128
    n=2**a
    for m in range(2,260):
        p=n*m+1
        if p>140000: break
        if not isprime(p): continue
        r=n/sqrt(p)
        # focus on the heavy band and a few generic
        if not (0.15<r<0.7 or m%37==0): continue
        M=Mval(p,n)
        if M is None: continue
        C=M/sqrt(n*log(p))
        v=0; t=p-1
        while t%2==0: t//=2; v+=1
        results.append((C,n,p,m,v,n/sqrt(p)))
results.sort(reverse=True)
print(f"scanned {len(results)} (n,p), heavy band n/sqrt(p) in [0.15,0.7]")
print(f"{'C':>6} {'n':>5} {'p':>7} {'idx':>5} {'v2':>3} {'n/sqrtp':>8}")
for C,n,p,m,v,r in results[:12]:
    print(f"{C:6.3f} {n:5d} {p:7d} {m:5d} {v:3d} {r:8.3f}")
print(f"\nGLOBAL MAX C = M/sqrt(n ln p) = {results[0][0]:.4f}   C<=2 holds: {results[0][0]<2}")
