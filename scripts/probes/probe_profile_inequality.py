#!/usr/bin/env python3
"""
PROBE (#389): the PROFILE-INEQUALITY / tower-extremality test.

Fleet live conjecture (lalalune 21:02 + TwoPowerFibreValue): the worst-case deep RS list over
mu_n (2-power) is attained by the 2-term TOWER word, with value the antipodal subset-sum fibre
    N_fib(2^{h+1}, r) = C(2^h - r%2, floor(r/2))      (n = 2^{h+1}, r = agreement param).
So the claim is: max over ALL words w of list(w, a) == max over towers == N_fib(n, a).

TEST: hill-climb the worst-case PLAIN RS list  list(w,a)=#{deg<k poly p : agreement(eval p,w)>=a}
over all words w on mu_n, and compare to N_fib(n,a). If hill-climb > N_fib at some past-Johnson a,
a NON-tower word beats the towers => the tower family is NOT the extremizer (refutation / flag).
(Caveat reported honestly: this is the plain agreement list; if the fleet's N_fib bounds a
different object (interleaved super-code list / deep-band supply M(w)), the comparison flags a
quantity mismatch rather than a refutation.)
"""
import math, random
from itertools import product

def cw(co, D, p):
    o=[]
    for x in D:
        v=0;xp=1
        for c in co: v=(v+c*xp)%p; xp=(xp*x)%p
        o.append(v)
    return tuple(o)
def all_cws(D,k,p): return [cw(co,D,p) for co in product(range(p),repeat=k)]
def lst(f,C,a): return sum(1 for c in C if sum(1 for i in range(len(f)) if c[i]==f[i])>=a)
def maxlist(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p);n=len(D);best=0
    for _ in range(rs):
        f=[rng.randrange(p) for _ in range(n)];cur=lst(f,C,a)
        for _ in range(cl):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=lst(f,C,a)
            if nl>=cur:cur=nl
            else:f[i]=old
        best=max(best,cur)
    return best
def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None: return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None
def Nfib(n,a):
    # antipodal tower fibre, n = 2^{h+1}, 2^h = n//2
    return math.comb(n//2 - (a%2), a//2)

def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None: print(f"(p={p} n={n}: no mu_n)",flush=True);return
    assert (n & (n-1))==0, "n must be 2-power"
    J=math.sqrt(n*k)
    print(f"\np={p} n={n}=2^{n.bit_length()-1} k={k}  Johnson sqrt(nk)={J:.2f}  (cw={p**k})",flush=True)
    print(f"   {'a':>2} {'pastJ':>5} | {'maxlist(all w)':>14} {'N_fib(tower)':>12} {'verdict':>22}",flush=True)
    for a in range(k+1, math.ceil(J)+1):
        ml=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        nf=Nfib(n,a)
        verdict = "maxlist>N_fib: NOT extremal" if ml>nf else ("= (tight)" if ml==nf else "<= N_fib (ok)")
        print(f"   {a:>2} {'PAST' if a<J else '  - ':>5} | {ml:>14} {nf:>12} {verdict:>22}",flush=True)
    print(flush=True)

if __name__=="__main__":
    run(p=97, n=8,  k=2, rs=120, cl=40)   # mu_8 in F_97 (proper subgroup)
    run(p=97, n=16, k=2, rs=40,  cl=60)   # mu_16 in F_97
    run(p=193,n=16, k=2, rs=30,  cl=60)
    print("===PROFDONE===",flush=True)
