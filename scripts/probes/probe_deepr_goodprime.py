"""
The decisive question: do GOOD primes ~n^4 stay good at DEEP r? Compute W_r exactly (convolution) for
r up to 8 for several primes near n^4=65536. If good primes stay W_r=0 deeper, good-prime existence at
depth log p is plausible; if they go bad at deeper r, the good fraction shrinks (the real difficulty).
"""
from collections import Counter
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
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def Er_upto(p,n,R):
    S=subgroup(p,n); c=Counter({0:1}); out={}
    for r in range(1,R+1):
        nc=Counter()
        for v,mm in c.items():
            for x in S: nc[(v+x)%p]+=mm
        c=nc
        out[r]=sum(mm*mm for mm in c.values())
    return out
n=16; R=8
# char-0 ref via big prime
q=10**9
while not(q%n==1 and isprime(q)): q+=1
E0=Er_upto(q,n,R)
print(f"n={n} char-0 (p={q}): "+", ".join(f"E_{r}={E0[r]}" for r in range(2,R+1)))
print()
print(f"W_r=E_r(F_p)-E_r(char0) for primes near n^4, r=2..{R}:")
print(f"{'p':>8} "+" ".join(f"W_{r:>2}" for r in range(2,R+1))+"  first-bad-r")
tested=0
for p in range(n**4, n**4+4000):
    if p%n==1 and isprime(p):
        E=Er_upto(p,n,R)
        Ws=[E[r]-E0[r] for r in range(2,R+1)]
        fb=next((r for r in range(2,R+1) if E[r]!=E0[r]), None)
        print(f"{p:>8} "+" ".join(f"{w:>4}" for w in Ws)+f"   {'r='+str(fb) if fb else 'GOOD to '+str(R)}")
        tested+=1
        if tested>=10: break
