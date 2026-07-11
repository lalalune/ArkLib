"""
Attack the 2 remaining open routes:
(A) ROOT-NUMBER lag-2 autocorrelation: does it PERSIST (=> structure=lead) or WASH OUT (=> artifact=wall)?
    Test at multiple (n,p), larger m, and check if it's a finite-size effect.
(B) DYADIC-NORM recursion at MATCHED thinness: W_r(mu_n) vs W_r(mu_{2n}) at primes with the SAME p/n^4.
"""
import cmath, math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primroot(p):
    facs=set(); mm=p-1; d=2
    while d*d<=mm:
        while mm%d==0: facs.add(d); mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs): return g
def gauss(p,g,k):
    tot=0j; x=1; w=2*math.pi/p; wc=2*math.pi/(p-1)
    for j in range(p-1):
        tot += cmath.exp(1j*wc*k*j)*cmath.exp(1j*w*x); x=x*g%p
    return tot
print("(A) root-number lag-2 autocorrelation across (n,p) -- persists or washes out?")
print(f"{'n':>4} {'p':>7} {'m':>5} {'|A(1)|':>8} {'|A(2)|':>8} {'|A(3)|':>8} {'1/sqrt(m)':>10}")
for n in (8,16):
    for pmul in (1,2,3):
        p=n*pmul*200+1
        while not(p%n==1 and isprime(p)): p+=1
        if p>4000: continue
        g=primroot(p); m=(p-1)//n
        W={t: gauss(p,g,(n*t)%(p-1))/math.sqrt(p) for t in range(1,m)}
        def A(k):
            return abs(sum(W[t]*W[(t+k-1)%(m-1)+1].conjugate() for t in range(1,m))/(m-1))
        print(f"{n:>4} {p:>7} {m:>5} {A(1):>8.4f} {A(2):>8.4f} {A(3):>8.4f} {1/math.sqrt(m):>10.4f}")
print("  => if |A(2)| stays ~2-3x white-noise across primes -> STRUCTURE; if it scatters/shrinks -> artifact.")
