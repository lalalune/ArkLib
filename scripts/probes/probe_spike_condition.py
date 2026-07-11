#!/usr/bin/env python3
"""
THE B=n SPIKE and the exact INDEX-semiprimitive law.

Observations from probe_true_semiprimitive:
  * B ~ sqrt(q) (BAD) happens iff -1 in <p> mod k, k=(q-1)/n the INDEX. Needs k small => n FAT.
  * Occasionally B = n EXACTLY (a perfectly in-phase coset): e.g. n=16,p=17 (q=289,k=18),
    n=16,p=97,113. We characterize these.

B = n means: exists coset c with eta_{c} = n, i.e. psi(c*y) = 1 for ALL y in mu_n,
i.e. Tr(c*y) = 0 for all y in mu_n  <=>  c*mu_n  subset  ker(Tr) (the trace-0 hyperplane,
size q/p).  Since |mu_n|=n, this needs n <= q/p AND mu_n*c additively closed in ker Tr.
For q=p^2, ker Tr = {b*alpha : b in F_p} (the 'imaginary axis'), size p.  So eta=n=p? no.
Actually Tr(a+b alpha)=2a, ker = {b alpha}.  c*mu_n in ker Tr means every elt of c*mu_n is
a pure alpha-multiple. c*mu_n is a coset of mu_n; it lies in the 1-diml F_p-subspace {b alpha}
minus 0 (which has p-1 nonzero elts) iff mu_n (times c) = a subgroup-coset inside that line's
multiplicative structure.  The line F_p*alpha is NOT multiplicatively closed in general...
but {b alpha : b in F_p^*} = alpha * F_p^*; alpha*F_p^* is a coset of F_p^* (the prime subfield
units). So c*mu_n subset alpha*F_p^*  <=>  mu_n subset (c^{-1} alpha) F_p^*  <=> mu_n subset a
single coset of F_p^*.  F_p^* has order p-1, index p+1 in F_q^*. mu_n in one coset of F_p^*
<=> n | p-1?? No: mu_n (order n) lies in a coset of F_p^* (order p-1) iff mu_n is a subset of
g^j F_p^* for some j, iff the image of mu_n in F_q^*/F_p^* (cyclic order p+1) is trivial-ish.
The quotient F_q^*/F_p^* is cyclic of order p+1. mu_n maps to the subgroup of order
n/gcd(n,p-1)... = n's image. mu_n in ONE coset of F_p^* <=> mu_n subset F_p^* (then j=0) OR mu_n's
image is a single point => image order 1 => n | p-1.  THE SPIKE B=n happens when n | p-1
(mu_n already in the prime field's multiplicative line up to the alpha twist) -- let's TEST.

We compute, for each (p,n) with n|p^2-1: B, and flags n|(p-1), n|(p+1), and check spike.
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
def qnr(p):
    for u in range(2,p):
        if pow(u,(p-1)//2,p)==p-1: return u
    raise RuntimeError
def gf2_mul(x,y,u,p):
    a,b=x;c,d=y; return ((a*c+b*d*u)%p,(a*d+b*c)%p)
def gf2_pow(x,e,u,p):
    r=(1,0)
    while e>0:
        if e&1: r=gf2_mul(r,x,u,p)
        x=gf2_mul(x,x,u,p); e>>=1
    return r
def find_gen_gf2(p,u):
    order=p*p-1; pf=list(factorize(order).keys())
    tries=[(a,b) for a in range(p) for b in range(p) if (a,b)!=(0,0)]; random.shuffle(tries)
    for g in tries:
        if all(gf2_pow(g,order//pr,u,p)!=(1,0) for pr in pf): return g
    raise RuntimeError
def gauss_absq(p,n):
    order=p*p-1; u=qnr(p); g=find_gen_gf2(p,u); k=order//n
    exp_t=[None]*order; cur=(1,0)
    for i in range(order): exp_t[i]=cur; cur=gf2_mul(cur,g,u,p)
    mu=[exp_t[(k*j)%order] for j in range(n)]
    w=2*math.pi/p; absq=[]
    for c in range(k):
        bc=exp_t[c%order]; s=0j
        for y in mu: prod=gf2_mul(bc,y,u,p); s+=cmath.exp(1j*w*(2*prod[0]%p))
        absq.append(abs(s)**2)
    return absq,k

if __name__=="__main__":
    random.seed(3)
    print("### B=n SPIKE characterization (q=p^2). flags: n|(p-1), n|(p+1).")
    print(f"{'n':>4} {'p':>5} {'q':>7} {'B':>8} {'B/n':>6} {'B=n?':>6} {'n|p-1':>6} {'n|p+1':>6} {'n|p^2-1only':>11}")
    for n in [8,16,32]:
        for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127]:
            if not is_prime(p): continue
            if (p*p-1)%n!=0: continue
            absq,k=gauss_absq(p,n)
            B=math.sqrt(max(absq))
            spike = abs(B-n)<1e-6
            f1 = (p-1)%n==0
            f2 = (p+1)%n==0
            only = (not f1) and (not f2)
            mark = "<==SPIKE" if spike else ""
            print(f"{n:>4} {p:>5} {p*p:>7} {B:>8.3f} {B/n:>6.3f} {str(spike):>6} {str(f1):>6} {str(f2):>6} {str(only):>11} {mark}")
        print()
    print("### HYPOTHESIS: B=n exactly  <=>  n | (p+1)  (mu_n lies in the norm-1 / 'imaginary' line)")
    print("###  -- these are the WORST designed q for q=p^2: pick p = -1 mod n  => B=n=sqrt(q)*..")
