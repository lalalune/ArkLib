import numpy as np
from math import gcd, log, sqrt

def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
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

def fact2(k):
    r=1
    for j in range(1,2*k,2): r*=j
    return r

def subgroup(p,n):
    e=(p-1)//n
    for cand in range(2,p):
        h=pow(cand,e,p)
        if h==1 or pow(h,n//2,p)==1: continue
        S=set(); x=1
        for _ in range(n): x=(x*h)%p; S.add(x)
        if len(S)==n: return np.array(sorted(S))
    raise RuntimeError

def heaviness(p,n):
    S=subgroup(p,n); b=np.arange(p)
    eta=np.zeros(p,dtype=complex); ang=2j*np.pi/p
    for x in S: eta+=np.exp(ang*((b*x)%p))
    mag2=np.abs(eta[1:])**2
    M=sqrt(mag2.max())
    # cumulant ratio at r=5
    Sr=(mag2**5).sum(); cr5=(Sr/p)/(fact2(5)*n**5)
    return M/sqrt(n), cr5

print("=== Heaviness vs n, log2(p)/log2(n) ratio, for FERMAT vs GENERIC ===")
print("Hypothesis: heavy when n^2/p large? or n/sqrt(p)? Test across families.\n")

# Fermat primes
print("FERMAT p=65537 (p-1=2^16), all n=2^a:")
for a in range(2,9):
    n=2**a
    if (65537-1)%n: continue
    Msn,cr5=heaviness(65537,n)
    print(f"  n={n:4d} (2^{a})  idx={(65536)//n:5d}  n/√p={n/sqrt(65537):.3f}  M/√n={Msn:.2f}  cum_r5={cr5:.2f}")

print("\nFERMAT p=257 (p-1=2^8), all n=2^a:")
for a in range(2,7):
    n=2**a
    if (256)%n: continue
    Msn,cr5=heaviness(257,n)
    print(f"  n={n:4d} (2^{a})  idx={256//n:5d}  n/√p={n/sqrt(257):.3f}  M/√n={Msn:.2f}  cum_r5={cr5:.2f}")

print("\nGENERIC primes (large odd part), n=64, varying p:")
for tgt in [4,8,16,32,64,128,256,512]:
    n=64
    p=None
    for m in range(tgt,tgt*4):
        cand=n*m+1
        if isprime(cand):
            # require substantial odd part
            op=cand-1
            while op%2==0: op//=2
            if op>=3:
                p=cand; break
    if p is None: continue
    Msn,cr5=heaviness(p,n)
    print(f"  p={p:8d}  idx≈{(p-1)//n:5d}  n/√p={n/sqrt(p):.3f}  M/√n={Msn:.2f}  cum_r5={cr5:.2f}")
