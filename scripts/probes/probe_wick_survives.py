"""
THE decisive computation: does E_r(F_p) <= Wick_r=(2r-1)!!*n^r hold at prize primes for DEEP r, even though
W_r>0? The prize needs E_r<=Wick (NOT W_r=0). Compute the RATIO E_r(F_p)/Wick_r for r=2..9 at primes ~n^4.
If ratio stays <1, the prize bound HOLDS at that prime (W_r is within the slack). This is the real condition.
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
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
n=16; R=9
print(f"n={n}: ratio E_r(F_p)/Wick_r, Wick_r=(2r-1)!!*{n}^r. <1 => prize bound HOLDS at that prime.")
print(f"{'p':>8} "+" ".join(f"r={r}" for r in range(2,R+1)))
tested=0
for p in [65537, 65617, 65809, 66161, 70001]:
    while not(p%n==1 and isprime(p)): p+=1
    E=Er_upto(p,n,R)
    ratios=[E[r]/(dfac(r)*n**r) for r in range(2,R+1)]
    print(f"{p:>8} "+" ".join(f"{x:.3f}" for x in ratios))
print()
print("=> if all ratios <1, E_r<=Wick HOLDS at deep r despite W_r>0: the prize bound is satisfied at these")
print("   primes (W_r is within slack). The 'W_r=0 good prime' framing was TOO STRICT; real condition E_r<=Wick.")
