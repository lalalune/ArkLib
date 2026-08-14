#!/usr/bin/env python3
"""#407 CRACK 4: r=2 char-p excess E2(mu_n) > 3n^2-3n (GenuineQuadruple) at GENUINE prize-shaped
primes (beta>=4, m=(p-1)/n odd, NOT Fermat) -- never run before (only Fermat beta=2.67).
E2 = #{(x1,x2,y1,y2) in mu_n^4: x1+x2=y1+y2 mod p} = sum_s c_s^2, c_s=#{pairs summing to s}.
char-0 value (n even, -1 in mu_n) = 3n^2-3n. Excess = char-p spurious 2-subset-sum coincidences."""
import numpy as np
from sympy import isprime
def E2(p,n):
    fac=set();x=p-1;d=2
    while d*d<=x:
        while x%d==0:fac.add(d);x//=d
        d+=1
    if x>1:fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac):g+=1
    h=pow(g,(p-1)//n,p);grp=[];cur=1
    for _ in range(n):grp.append(cur);cur=cur*h%p
    grp=np.array(grp)
    sums=(grp[:,None]+grp[None,:])%p          # n x n sum table
    cnt=np.bincount(sums.ravel(),minlength=p)
    return int((cnt.astype(np.int64)**2).sum())
print(f"{'n':>4} {'p':>10} {'beta':>5} {'m odd?':>6} {'E2':>9} {'3n^2-3n':>9} {'excess':>7}")
print("-"*58)
for n in [8,16,32]:
    char0=3*n*n-3*n
    mmin=n**3                                  # p>=n^4
    m=mmin if mmin%2==1 else mmin+1
    got=0
    while got<6:
        p=n*m+1
        if p>20_000_000:break
        if isprime(p):
            e2=E2(p,n);beta=np.log(p)/np.log(n)
            print(f"{n:>4} {p:>10} {beta:>5.2f} {'yes':>6} {e2:>9} {char0:>9} {e2-char0:>7}")
            got+=1
        m+=2
        if n>=32:m+=2*((n**3)//300)
    print()
print("VERDICT: excess=0 everywhere => r=2 moment base CLEAN at prize-shaped primes (GenuineQuadruple")
print("FALSE in-regime, anchors the ladder). excess>0 => the r=2 char-p excess is REAL at prize shape.")
