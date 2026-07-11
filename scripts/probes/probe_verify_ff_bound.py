"""
Rigorously check: is A_r <= (2r-1)!!*(n)_r (the falling-factorial bound) actually TRUE? And the binomial EGF?
And what is the RIGHT open input — is it W_r <= slack_r where slack_r = Wick - E_r^char0 ?
"""
from collections import Counter
import math
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
def Er(p,n,R):
    c=Counter({0:1}); E={}; S=subgroup(p,n)
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc; E[r]=sum(m*m for m in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
def falling(n,r):
    p=1
    for j in range(r): p*=(n-j)
    return p
def E0cf(r,n):
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n,
            6:10395*n**6-155925*n**5+1022175*n**4-3534300*n**3+6246471*n**2-4370520*n,
            7:135135*n**7-2837835*n**6+26801775*n**5-141891750*n**4+433726293*n**3-708996288*n**2+471556800*n}[r]
print("Q1: is A_r <= (2r-1)!!(n)_r (falling-factorial bound)? [A_r=DC-subtracted char-p energy]")
for n,p in [(16,65537),(32,1048609)]:
    E=Er(p,n,7)
    print(f" n={n} p={p}:")
    for r in range(2,8):
        Ar=E[r]-n**(2*r)/p; ff=dfac(r)*falling(n,r); wick=dfac(r)*n**r
        print(f"   r={r}: A_r/Wick={Ar/wick:.4f}  ff/Wick={ff/wick:.4f}  A_r<=ff? {Ar<=ff}  A_r<=Wick? {Ar<=wick}")
print()
print("Q2: the RIGHT decomposition: A_r <= Wick <=> W_r <= slack_r, slack_r = Wick - E_r^char0 ~ Wick(1-exp(-r^2/2n)):")
for n,p in [(16,65537)]:
    E=Er(p,n,7)
    print(f" n={n} p={p}:")
    for r in range(2,8):
        wick=dfac(r)*n**r; E0=E0cf(r,n); Wr=E[r]-E0; slack=wick-E0
        dc=n**(2*r)/p
        # A_r = E_r(F_p)-dc = E0 + W_r - dc. A_r<=Wick <=> W_r <= Wick-E0+dc = slack+dc
        print(f"   r={r}: W_r={Wr}  slack_r=Wick-E0={slack}  slack/Wick={slack/wick:.4f}(~r^2/2n={r*r/(2*n):.3f})  W_r<=slack+dc? {Wr<=slack+dc}")
print()
print("=> the falling-factorial bound A_r<=(2r-1)!!(n)_r status; the prize's TRUE form = W_r <= slack_r(+dc).")
print("   slack_r/Wick ~ 1-exp(-r^2/2n) ~ r^2/2n (GROWING) = the room the wraparound has. This is the right input.")
