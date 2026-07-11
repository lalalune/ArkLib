#!/usr/bin/env python3
"""
THE SEMIPRIMITIVE DICHOTOMY  (#389 designed-q core).

CLAIM TO TEST (Baumert-McEliece / Liu-Zhou Thm 116 / Podesta-Videla Thm 6.1):
  If  -1 in <p> mod n   (i.e. p^t = -1 mod n for some t; "semiprimitive"),
  then ALL Gauss periods eta_b have |eta_b| ~ sqrt(q)  (the LARGE / additively-structured case).
  Specifically with f = ord_n(p), f = 2t even, the k=(q-1)/n cosets give exactly TWO
  period values, and  |eta_b| in { ~ sqrt(q)*(small const) }  -> B ~ sqrt(q).  BAD: graph
  is far from Ramanujan; B/sqrt(n) ~ sqrt(q/n) -> infinity as q/n -> infinity.

  Conversely, when -1 NOT in <p> (generic / "non-semiprimitive"), measured B ~ sqrt(n log(q/n)).

This script:
 (1) For n=2^mu, builds the SEMIPRIMITIVE family explicitly: choose p = -1 mod n (so t=1,
     f=2, immediately semiprimitive), build F_q = F_{p^2}, compute B, show B/sqrt(q) is O(1)
     i.e. B ~ sqrt(q) >> sqrt(n).  THE BAD DESIGNED FAMILY.
 (2) Shows the period takes few values (additively structured).
 (3) Contrasts B/sqrt(q) (semiprim, -> const) vs B/sqrt(n) and the question whether ANY
     designed family gives B ~ sqrt(n).

Field arithmetic: GF(p^2) is cheap (a + b*alpha, alpha^2 = nonresidue).  We pick a quadratic
nonresidue u, F_{p^2} = F_p[alpha]/(alpha^2 - u).  Trace_{F_{p^2}/F_p}(a+b alpha) = 2a.
(Because the conjugate of a+b alpha is a-b alpha, sum = 2a.)
psi(z) = exp(2 pi i Tr(z)/p) = exp(2 pi i * 2a / p).
"""
import cmath, math, random
from collections import Counter

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f

def ord_mod(a,n):
    a%=n
    if math.gcd(a,n)!=1: return None
    o=1;x=a%n
    while x!=1: x=x*a%n; o+=1
    return o

def qnr(p):
    # a quadratic non-residue mod p
    for u in range(2,p):
        if pow(u,(p-1)//2,p)==p-1: return u
    raise RuntimeError

# GF(p^2): element (a,b) = a + b*alpha, alpha^2=u
def gf2_mul(x,y,u,p):
    a,b=x; c,d=y
    # (a+b α)(c+d α) = ac + bd u + (ad+bc) α
    return ((a*c+b*d*u)%p, (a*d+b*c)%p)
def gf2_pow(x,e,u,p):
    r=(1,0)
    while e>0:
        if e&1: r=gf2_mul(r,x,u,p)
        x=gf2_mul(x,x,u,p); e>>=1
    return r

def find_gen_gf2(p,u):
    q=p*p; order=q-1
    pf=list(factorize(order).keys())
    cand=[]
    import itertools
    tries=[(a,b) for a in range(p) for b in range(p) if (a,b)!=(0,0)]
    random.shuffle(tries)
    for g in tries:
        if all(gf2_pow(g,order//pr,u,p)!=(1,0) for pr in pf):
            return g
    raise RuntimeError("no gen")

def gauss_B_gf2(p,n,full=False):
    q=p*p; order=q-1
    assert order%n==0
    u=qnr(p)
    g=find_gen_gf2(p,u)
    k=order//n
    # precompute exp table
    exp_t=[None]*order
    cur=(1,0)
    for i in range(order):
        exp_t[i]=cur; cur=gf2_mul(cur,g,u,p)
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p
    absq=[]
    for c in range(k):
        bc=exp_t[c%order]
        s=0j
        for y in mu:
            prod=gf2_mul(bc,y,u,p)
            tr=(2*prod[0])%p           # Tr(a+bα)=2a
            s+=cmath.exp(1j*w*tr)
        absq.append(abs(s)**2)
    B=math.sqrt(max(absq))
    vals=Counter(round(a,2) for a in absq)
    return B,k,vals,absq

if __name__=="__main__":
    import sys
    print("### SEMIPRIMITIVE BAD FAMILY:  q=p^2 with p = -1 mod n  =>  f=ord_n(p)=2, -1=p in <p>")
    print("### Theory predicts B ~ sqrt(q)  (NOT sqrt(n)) : the graph is FAR from Ramanujan.")
    print(f"{'n':>4} {'p':>6} {'q=p^2':>9} {'k':>7} {'#vals':>6} {'B':>9} {'B/sqrtn':>9} {'B/sqrtq':>9} {'sqrt(q)':>9} {'periodvals(top3)':>30}")
    for n in [8,16,32]:
        mu=int(math.log2(n))
        # primes p = -1 mod n  (=> n | p+1 | p^2-1, and p mod n = n-1, ord_n(p)=2, -1=p^1 in <p>)
        cnt=0
        p = n-1
        while cnt<6:
            p+=n
            cand=p  # p = n-1 + n*t  => p = -1 mod n
            if cand>4000: break
            if is_prime(cand):
                p_=cand
                B,k,vals,absq=gauss_B_gf2(p_,n)
                top=sorted(vals.items(),key=lambda kv:-kv[1])[:3]
                q=p_*p_
                print(f"{n:>4} {p_:>6} {q:>9} {k:>7} {len(vals):>6} {B:>9.3f} "
                      f"{B/math.sqrt(n):>9.3f} {B/math.sqrt(q):>9.3f} {math.sqrt(q):>9.2f} "
                      f"  {str(top):>28}")
                cnt+=1
        print()
    print("### INTERPRETATION:")
    print("  If B/sqrt(q) is bounded BELOW by a positive constant as p grows (n fixed), the")
    print("  semiprimitive family is provably NON-Ramanujan: B ~ sqrt(q) = sqrt(n)*sqrt(q/n) >> sqrt(n).")
    print("  These are the BAD designed-q's: choose p = -1 mod n and you MAXIMIZE the Gauss period.")
