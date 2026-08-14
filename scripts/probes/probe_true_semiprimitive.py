#!/usr/bin/env python3
"""
THE TRUE SEMIPRIMITIVE CONDITION (correcting the naive '-1 in <p> => B~sqrt q').

Baumert-McEliece-Rumsey "uniform cyclotomy": the Gauss periods of the INDEX-k subgroup
(here mu_n, with INDEX k=(q-1)/n) take ~ O(1) values of size ~ sqrt(q) IFF the relevant
*GAUSS SUM* g(chi) is a rational/known multiple of sqrt(q) for the order-k characters chi
trivial on mu_n.  The classical "semiprimitive" theorem is about the INDEX:

  SEMIPRIMITIVE (Baumert-McEliece): let N=k be the INDEX = order of the character chi
  trivial on mu_n  (chi has order k).  If there is t with  p^t = -1 mod k,  then the
  Gauss sum g(chi) is an EXPLICIT multiple of sqrt(q): g(chi) = +- p^{...} sqrt(q),
  hence the periods over mu_n (which is the kernel) are ~ sqrt(q)/n * (stuff) ... and the
  graph eigenvalue ~ sqrt(q).  The condition is on  p mod k = p mod (q-1)/n,  NOT p mod n.

So the relevant modulus is  k = (q-1)/n  (the INDEX), not n.  For thin n (prize), k is HUGE
(~ q/n ~ q^{1-gamma}), and "p^t = -1 mod k" is a very restrictive condition.

We TEST which q actually trigger the semiprimitive sqrt(q) blow-up, by checking:
   does max_b |eta_b| / sqrt(q) stay bounded BELOW (semiprimitive, BAD)  vs  -> 0 (generic)?
and correlating with  ord_k(p)  and  '-1 in <p> mod k'  (k = INDEX).

GF(p^2) only (cheap); we scan many p and for each compute eta and the index-semiprimitive flag.
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
    if n==1: return 1
    if math.gcd(a,n)!=1: return None
    o=1;x=a%n
    while x!=1: x=x*a%n; o+=1
    return o

def neg1_in_powers(a,n):
    # is -1 in <a> mod n?  return t with a^t=-1 mod n, else None
    if n<=2: return None
    a%=n; x=a; t=1
    target=(n-1)%n
    seen=0
    while seen< 2*n:
        if x==target: return t
        if x==1: return None
        x=x*a%n; t+=1; seen+=1
    return None

def qnr(p):
    for u in range(2,p):
        if pow(u,(p-1)//2,p)==p-1: return u
    raise RuntimeError

def gf2_mul(x,y,u,p):
    a,b=x; c,d=y
    return ((a*c+b*d*u)%p,(a*d+b*c)%p)
def gf2_pow(x,e,u,p):
    r=(1,0)
    while e>0:
        if e&1: r=gf2_mul(r,x,u,p)
        x=gf2_mul(x,x,u,p); e>>=1
    return r
def find_gen_gf2(p,u):
    order=p*p-1; pf=list(factorize(order).keys())
    tries=[(a,b) for a in range(p) for b in range(p) if (a,b)!=(0,0)]
    random.shuffle(tries)
    for g in tries:
        if all(gf2_pow(g,order//pr,u,p)!=(1,0) for pr in pf): return g
    raise RuntimeError

def gauss_B_gf2(p,n):
    order=p*p-1; assert order%n==0
    u=qnr(p); g=find_gen_gf2(p,u); k=order//n
    exp_t=[None]*order; cur=(1,0)
    for i in range(order): exp_t[i]=cur; cur=gf2_mul(cur,g,u,p)
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p; absq=[]
    for c in range(k):
        bc=exp_t[c%order]; s=0j
        for y in mu:
            prod=gf2_mul(bc,y,u,p); s+=cmath.exp(1j*w*(2*prod[0]%p))
        absq.append(abs(s)**2)
    return math.sqrt(max(absq)),k,absq

if __name__=="__main__":
    random.seed(7)
    print("### q=p^2.  INDEX k=(q-1)/n.  Semiprimitive iff -1 in <p mod k>.")
    print("### Question: does that flag predict B ~ sqrt(q) (bad) vs B ~ sqrt(n) (good)?")
    for n in [8,16]:
        print(f"\n--- n={n} ---")
        print(f"{'p':>6} {'q':>9} {'k=index':>9} {'-1 in <p mod k>?':>17} {'ord_k(p)':>9} {'B':>9} {'B/sqrtn':>9} {'B/sqrtq':>9}")
        cnt=0; p=2
        while cnt<14 and p<3000:
            p+=1
            if not is_prime(p): continue
            if (p*p-1)%n!=0: continue
            k=(p*p-1)//n
            B,kk,absq=gauss_B_gf2(p,n)
            t=neg1_in_powers(p,k)
            sp = t is not None
            ok=ord_mod(p%k,k) if math.gcd(p,k)==1 else None
            print(f"{p:>6} {p*p:>9} {k:>9} {str(sp):>17} {str(ok):>9} {B:>9.3f} {B/math.sqrt(n):>9.3f} {B/math.sqrt(p*p):>9.4f}")
            cnt+=1
    print("\n### NOTE: for thin n, k=(q-1)/n is huge; -1 in <p mod k> is rare.  When it does")
    print("### NOT hold, periods are generic.  The classical sqrt(q) blow-up needs k | p^t+1,")
    print("### i.e. k small i.e. n ~ q (FAT). Confirm by also showing a FAT-n semiprimitive case.")
    print("\n### FAT-n semiprimitive demo: pick k small with -1 in <p mod k>, n=(q-1)/k LARGE.")
    print(f"{'p':>6} {'k':>5} {'n=(q-1)/k':>10} {'gamma':>7} {'-1in<p,k>':>10} {'B':>9} {'B/sqrtn':>9} {'B/sqrtq':>9}")
    for p in [7,11,13,17,19,23,29,31,37,41,43,47]:
        if not is_prime(p): continue
        q=p*p
        for k in [3,4,5,6,8]:
            if (q-1)%k!=0: continue
            n=(q-1)//k
            if n<2: continue
            t=neg1_in_powers(p,k)
            if t is None: continue   # only semiprimitive
            try: B,kk,absq=gauss_B_gf2(p,n)
            except Exception: continue
            gamma=math.log(n)/math.log(q)
            print(f"{p:>6} {k:>5} {n:>10} {gamma:>7.3f} {str(True):>10} {B:>9.3f} {B/math.sqrt(n):>9.3f} {B/math.sqrt(q):>9.4f}")
