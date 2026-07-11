"""
(1) What divisibility does the REAL symmetry (swap x<->y, negation x->-x) give for W_r? (replaces dead Idea A)
(2) Idea B test: does the BAD-PRIME SET telescope along the cyclotomic tower? Compare bad primes for
    E_r(mu_n) vs E_r(mu_{n/2}) -- is bad(2n) related to bad(n)?
"""
import itertools
from collections import Counter
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
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
def primes1modn(n,lo,hi):
    return [p for p in range(lo,hi) if p%n==1 and isprime(p)]
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def E_r(p,n,S,r):
    cc=Counter()
    for combo in itertools.product(S,repeat=r): cc[sum(combo)%p]+=1
    return sum(v*v for v in cc.values())

# (1) divisibility of W_r
n=8
bp=primes1modn(n,10**7,10**7+10000)[0]; Sb=subgroup(bp,n)
E0={r:E_r(bp,n,Sb,r) for r in (2,3)}
print("(1) W_r divisibility (n=8): the swap+negation symmetry gives what divisor?")
for p in primes1modn(n,9,400):
    S=subgroup(p,n)
    for r in (2,3):
        W=E_r(p,n,S,r)-E0[r]
        if W>0:
            divs=[d for d in (2,4,8,16) if W%d==0]
            print(f"  p={p} r={r}: W={W}, divisible by {max(divs) if divs else 1}")
            break
print()
# (2) Idea B: bad-prime telescoping. bad(n) = primes p=1 mod n with E_2(F_p)!=E_2(char0). Compare n=8 vs n=16.
print("(2) Idea B: does the bad-prime set telescope along the tower? bad primes for E_2 at n=8 vs n=16:")
for n in (8,16):
    bp=primes1modn(n,10**7,10**7+20000)[0]; Sb=subgroup(bp,n)
    E2c0=E_r(bp,n,Sb,2)
    bad=[]
    for p in primes1modn(n, n+1, 5000):
        S=subgroup(p,n)
        if S and E_r(p,n,S,2)!=E2c0: bad.append(p)
    print(f"  n={n}: E_2(char0)={E2c0}; bad primes (E_2 wraparound) up to 5000: {bad}")
print("  => if bad(16) ⊆ bad(8) ∪ (new small set), the tower telescoping (Idea B) has structure.")
