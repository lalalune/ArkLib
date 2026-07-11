#!/usr/bin/env python3
"""Confirm a concrete char-p spurious vanishing witness at n=32, prime p=665857 (=1 mod 32)."""
import itertools, math, cmath

def antipodal_free(T,n):
    s=set(T); h=n//2
    return all((j+h)%n not in s for j in T)
def int_norm(T,n):
    prod=1.0+0j
    for a in range(1,n,2):
        s=sum(cmath.exp(1j*2*math.pi*((a*j)%n)/n) for j in T)
        prod*=s
    return round(prod.real)
def factor(x):
    x=abs(x); f={}; d=2
    while d*d<=x:
        while x%d==0: f[d]=f.get(d,0)+1; x//=d
        d+=1 if d==2 else 2
    if x>1: f[x]=f.get(x,0)+1
    return f

n=32; P=665857
print(f"P=665857: prime? ", all(P%d for d in range(2,2580)), " P mod 32 =", P%n)
# find an antipodal-free T of weight 6 with P | N(T)
found=None
for c in itertools.combinations(range(1,n),5):
    T=(0,)+c
    if not antipodal_free(T,n): continue
    N=int_norm(T,n)
    if N!=0 and N%P==0:
        found=(T,N); break
print("witness T=",found[0]," N=",found[1])
print("factor N=",factor(found[1]))
# Now verify directly: in F_P, with w a primitive 32nd root of unity, sum_{j in T} w^j == 0 ?
# find 32nd root of unity mod P
def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
assert isprime(P)
# primitive root
def proot(p):
    # factor p-1
    f=list(factor(p-1).keys())
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in f): return a
g=proot(P)
w=pow(g,(P-1)//n,P)
assert pow(w,n,P)==1 and pow(w,n//2,P)!=1
T=found[0]
for a in range(1,n,2):
    s=sum(pow(w,(a*j)%n,P) for j in T)%P
    if s==0:
        print(f"  CONFIRMED: sum_{{j in T}} w^({a}j) == 0 mod {P}  (conjugate a={a}) -- SPURIOUS char-p vanishing exists")
        break
