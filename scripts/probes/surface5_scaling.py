"""Confirm the load-bearing GEOMETRY claim: lambda_1^l1(p_0) scales like p^{1/d}, d=n/2.
This is what makes onset r* ~ (1/2) p^{1/d} -> the no-wrap depth, and the transfer:
needed depth ~ ln q = beta ln n  vs  onset ~ (1/2) p^{1/d} = (1/2) n^{2 beta/n}."""
import itertools
from math import log
def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def gen_root(p,n):
    def order(a):
        o=1;cur=a%p
        while cur!=1: cur=(cur*a)%p;o+=1
        return o
    prim=next(a for a in range(2,p) if order(a)==p-1)
    return pow(prim,(p-1)//n,p)
def lambda1_l1(p,n,Rmax):
    d=n//2;g=gen_root(p,n);gp=[pow(g,k,p) for k in range(d)]
    best=None
    for c in itertools.product(range(-Rmax,Rmax+1),repeat=d):
        if all(x==0 for x in c): continue
        if sum(ck*gpp for ck,gpp in zip(c,gp))%p==0:
            l1=sum(abs(x) for x in c)
            if best is None or l1<best: best=l1
    return best
print("lambda_1^l1(p_0) vs p^{1/d}  [d=n/2]")
print(f"{'n':>4}{'d':>3}{'p':>7}{'lam1_l1':>9}{'p^(1/d)':>9}{'ratio':>7}")
for n,Rmax,prange in [(4,15,[17,41,73,97,113,137,193,233,257,281]),
                      (8,4,[73,89,137,233,281,409,521,569,761]),
                      (16,3,[257,353,433,577,673,929,1153,1409])]:
    d=n//2
    for p in prange:
        if (p-1)%n: continue
        l1=lambda1_l1(p,n,Rmax)
        pd=p**(1.0/d)
        if l1: print(f"{n:>4}{d:>3}{p:>7}{l1:>9}{pd:>9.2f}{l1/pd:>7.2f}")
