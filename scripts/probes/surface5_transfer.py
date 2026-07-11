"""
SURFACE 5 — the precise transfer and where it RE-COLLAPSES to BGK.

KEY GEOMETRIC FACTS (established):
 * Q4>0 onset r* <=> the box of achievable r-difference coordinate-vectors contains a NONZERO
   point of the ideal lattice p_0 = ker(c |-> sum c_k g^k mod p), det(p_0)=p, dim d=n/2.
 * The shortest vector lambda_1(p_0) (euclidean) satisfies Minkowski lambda_1 <= sqrt(d) p^{1/d}.
   Measured: lambda_1 ~ p^{1/d} (and a SHORT lattice vector exists at length ~p^{1/d}).
 * An r-tuple DIFFERENCE alpha = (sum r roots) - (sum r roots) realizes coordinate-vector c with
   l1-norm sum|c_k| <= 2r (each of the 2r roots contributes +-1 to one coordinate via zeta^d=-1).
   So the set of REACHABLE alpha-coordinate-vectors at depth r is (subset of) the l1-ball of radius 2r.

THE ONSET LAW (geometry of numbers):
   r* = (1/2) * min { sum|c_k| : 0 != c in p_0 }  =  (1/2) * lambda_1^{(l1)}(p_0).
   i.e. Q4=0 for all r < (1/2) lambda_1^{l1}(p_0).
   Minkowski (l1 version): lambda_1^{l1}(p_0) <= d * p^{1/d}   (l1-ball volume (2t)^d/d!, det=p).
   => r* <= (d/2) p^{1/d}.   And a matching LOWER reach: NO p_0-point of l1-norm < lambda_1^{l1}.

WHAT THIS PROVES (the GOOD direction, the part that LANDS):
   For r < (1/2) lambda_1^{l1}(p_0):   Q4 = 0   EXACTLY   =>   E_r(F_p) = E_r^char0 = Wick.
   Hence  B^{2r} <= p * E_r = p * (2r-1)!! n^r   for ALL such r, with NO anomalous wrap mass.
   Minimizing the moment bound  B <= (p (2r-1)!! n^r)^{1/2r} over r gives the per-frequency
   carrier B <= sqrt(2 n ln q) PROVIDED the optimal r_opt ~ ln q stays BELOW the onset r*.

THE TRANSFER GAP (where it RE-COLLAPSES to BGK):
   r_opt ~ ln q = beta ln n  must be < r* ~ (d/2) p^{1/d} = (n/4) (n^beta)^{2/n} = (n/4) n^{2 beta/n}.
   As n -> infinity, n^{2beta/n} -> 1, so r* ~ n/4 -> infinity, and r_opt ~ beta ln n.
   => r_opt < r* HOLDS comfortably for large n  (ln n << n/4).
   *** SO THE GEOMETRY SAYS Q4=0 AT THE NEEDED DEPTH, AND THE WALL SHOULD FALL?? ***
   The catch: r* is an UPPER bound on the no-wrap depth ONLY IF the LOWER reach lambda_1^{l1} is
   actually ~ d p^{1/d}.  But lambda_1 can be as SMALL as O(d) (a SHORT l1 vector), in which case
   r* ~ O(d) = O(n) -- still >> ln n.  Either way r* >> r_opt.

   THE REAL GAP: Q4=0 controls only the b s.t. ALPHA is captured by p_0. But B = max_b |eta_b| ranges
   over ALL b != 0, i.e. over the |coordinate-evaluation at g^b| for d different primes p_b above p.
   E_r = (1/p) sum_b |eta_b|^{2r} aggregates ALL of them via Plancherel; the moment bound gives
   B^{2r} <= p E_r, and the b=0 term ALONE is eta_0 = n, contributing n^{2r} to p E_r.
   So  p E_r >= n^{2r}  ALWAYS  (moment no-go) =>  (p E_r)^{1/2r} >= n, NOT sqrt(2n ln q).
   *** The geometry gives Q4=0 (E_r EXACTLY Wick) but Wick itself has p*Wick >= n^{2r}: at r_opt~ln q,
       (p (2r-1)!! n^r)^{1/2r} ~ sqrt(2n ln q) ONLY if the n^{2r}/p (=b=0) term is SUBTRACTED first. ***
   The b=0 term is KNOWN (eta_0 = n exactly). The carrier is B = max over b != 0. We need
       max_{b!=0}|eta_b|^{2r} <= p E_r - n^{2r} = p*Wick - n^{2r} + p*Q4 = p*Wick - n^{2r}  (since Q4=0).
   So the WHOLE WALL, post-geometry, is the SINGLE inequality at r=r_opt:
       (p*Wick - n^{2r})^{1/2r}  <=  sqrt(2 n ln q)    [is p*Wick - n^{2r} ~ Wick-scale, not n^{2r}-scale?]
   This is exactly the moment-method closure, and it is TRUE numerically iff the (2r-1)!! n^r term
   DOMINATES n^{2r}/p, i.e. p (2r-1)!! n^r > n^{2r}, i.e. p (2r-1)!! > n^r.  At r~ln q=beta ln n,
   n^r = n^{beta ln n} = q^{ln n} -- ASTRONOMICAL, >> p=q.  So p*Wick - n^{2r} can be NEGATIVE-ish / the
   bound is dominated by the b=0 subtraction and DOES NOT close by Wick alone.

CONCLUSION: geometry of numbers CLEANLY proves Q4=0 to depth r* ~ n/4 (>> needed r_opt~ln q), i.e.
the energy E_r is EXACTLY the char-0 Wick value with NO wrap-around anomaly at every needed depth.
This REMOVES the 'Q4 anomaly' face entirely.  But it does NOT close the prize: after removing Q4,
the residual is p*Wick - n^{2r} = (the moment-no-go b=0 subtraction), and Wick's (2r-1)!! n^r is
ITSELF too large at r~ln q for the min to reach sqrt(2n ln q) -- the SAME moment-no-go / W4 wall.
The geometry kills the wrap-around face but lands BACK on BGK via the b=0 / Wick-scale gap.

Let's NUMERICALLY confirm the two halves:
 (A) onset r* matches (1/2) lambda_1^{l1}(p_0)   [geometry controls Q4 onset]
 (B) even with Q4=0, min_r (p*Wick)^{1/2r} and min_r (p*Wick - n^{2r})^{1/2r} vs sqrt(2 n ln q) and true B.
"""
import itertools, cmath
from collections import Counter
from fractions import Fraction
from math import factorial, log, sqrt

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

def subgroup(p,n):
    g=gen_root(p,n); S=[];cur=1
    for _ in range(n): S.append(cur);cur=(cur*g)%p
    return S

def antidiag(d,r):
    if d==0:
        if r==0: yield ()
        return
    for first in range(r+1):
        for rest in antidiag(d-1,r-first): yield (first,)+rest
def bessel(n,r):
    d=n//2;s=Fraction(0)
    for m in antidiag(d,r):
        prod=Fraction(1)
        for mi in m: prod*=Fraction(1,factorial(mi)**2)
        s+=prod
    return int(factorial(2*r)*s)
def E_r_modp(p,n,r):
    S=subgroup(p,n);cnt=Counter({0:1})
    for _ in range(r):
        new=Counter()
        for s,c in cnt.items():
            for x in S: new[(s+x)%p]+=c
        cnt=new
    return sum(c*c for c in cnt.values())

def lambda1_l1(p,n,Rmax=4):
    d=n//2; g=gen_root(p,n); gp=[pow(g,k,p) for k in range(d)]
    best=None
    for c in itertools.product(range(-Rmax,Rmax+1), repeat=d):
        if all(x==0 for x in c): continue
        if sum(ck*gpp for ck,gpp in zip(c,gp))%p==0:
            l1=sum(abs(x) for x in c)
            if best is None or l1<best: best=l1
    return best

def B_max(p,n):
    S=subgroup(p,n);best=0.0
    for b in range(1,p):
        s=sum(cmath.exp(2j*cmath.pi*(b*x%p)/p) for x in S)
        best=max(best,abs(s))
    return best

print("(A) ONSET LAW: measured Q4-onset r*  vs  ceil( lambda_1^{l1}(p_0) / 2 )")
print(f"{'n':>4}{'p':>6}{'onset r*':>9}{'lam1_l1':>9}{'ceil(l1/2)':>11}{'match':>7}")
for n in [4,8,16]:
    q3={r:bessel(n,r) for r in range(1,16)}
    primes=[x for x in range(n*n,80*n) if (x-1)%n==0 and is_prime(x)][:3]
    for p in primes:
        onset=next((r for r in range(1,15) if E_r_modp(p,n,r)-q3[r]>0), None)
        l1=lambda1_l1(p,n, Rmax=4 if n<=8 else 3)
        pred = (l1+1)//2 if l1 else None
        m = "Y" if (onset and pred and onset==pred) else ("~" if onset and pred and abs(onset-pred)<=1 else "N")
        print(f"{n:>4}{p:>6}{str(onset):>9}{str(l1):>9}{str(pred):>11}{m:>7}")

print()
print("(B) Post-geometry residual: even with Q4=0, does Wick alone close to sqrt(2 n ln q)?")
print(f"{'n':>4}{'p':>7}{'trueB':>9}{'sqrt(2nlnq)':>12}{'min(pWick)^1/2r':>16}{'min(pWick-n2r)^1/2r':>20}")
for n in [8,16]:
    p=next(x for x in range(n**3,4*n**3) if (x-1)%n==0 and is_prime(x))
    trueB=B_max(p,n)
    target=sqrt(2*n*log(p))
    def df(m):
        o=1
        while m>1: o*=m;m-=2
        return o
    best1=None;best2=None
    for r in range(1,40):
        wick=df(2*r-1)*n**r
        v1=(p*wick)**(1.0/(2*r))
        val2=p*wick - n**(2*r)
        v2=(val2)**(1.0/(2*r)) if val2>0 else float('inf')
        best1=v1 if best1 is None else min(best1,v1)
        best2=v2 if best2 is None else min(best2,v2)
    print(f"{n:>4}{p:>7}{trueB:>9.2f}{target:>12.2f}{best1:>16.2f}{best2:>20.2f}")
