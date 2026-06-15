import math
from sympy import isprime, primitive_root
from collections import Counter

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    assert len(set(S))==n
    return S

def stats(S,p):
    n=len(S)
    cnt=Counter((a+b)%p for a in S for b in S)
    ss=len(cnt); E2=sum(v*v for v in cnt.values())
    return ss,E2

# Use LARGE primes p ~ n^4 (prize-like beta) so no wraparound collapse
print(f"{'n':>4} {'beta~':>6} {'p':>14} {'|G+G|':>7} {'n2-n':>7} {'ss/n2':>7} {'E2':>9} {'E2/n2':>7} {'logE2/logn':>10}")
for n in [8,16,32,64,128]:
    target = n**4
    p=target
    # find prime p = 1 mod n near n^4
    cnt=0
    while cnt<2:
        if isprime(p) and (p-1)%n==0:
            S=subgroup(p,n); ss,E2=stats(S,p)
            beta=math.log(p)/math.log(n)
            print(f"{n:>4} {beta:>6.2f} {p:>14} {ss:>7} {n*n-n:>7} {ss/(n*n):>7.4f} {E2:>9} {E2/(n*n):>7.3f} {math.log(E2)/math.log(n):>10.4f}")
            cnt+=1
        p+=1
