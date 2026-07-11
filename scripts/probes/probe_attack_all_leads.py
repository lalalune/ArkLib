"""
Attack all remaining directions on the decay/slack:
(L1) Binomial-EGF conjecture: Sum_r [E_0/(2r-1)!!] t^r/r! <= (1+t)^n ?  [creative lead - test/refute]
(L2) W_r/slack_r ratio: does it approach 1 (danger) or stay bounded (favorable)? [the real open input]
(L3) slack growth: slack_r = Wick - E_0 ~ Wick*r^2/2n (derived). Verify + W_r growth rate vs slack.
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
def E0cf(r,n):
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n,
            6:10395*n**6-155925*n**5+1022175*n**4-3534300*n**3+6246471*n**2-4370520*n,
            7:135135*n**7-2837835*n**6+26801775*n**5-141891750*n**4+433726293*n**3-708996288*n**2+471556800*n}[r]
def falling(n,r):
    p=1
    for j in range(r): p*=(n-j)
    return p
print("(L1) Binomial-EGF: is Sum_r [E_0/(2r-1)!!] t^r/r! <= (1+t)^n? Equivalent: is E_0/(2r-1)!! <= (n)_r? (coeff-wise)")
for n in (16,32):
    print(f" n={n}: E_0/(2r-1)!! vs (n)_r=falling(n,r):")
    viol=False
    for r in range(2,8):
        lhs=E0cf(r,n)/dfac(r); rhs=falling(n,r)
        ok = lhs<=rhs
        if not ok: viol=True
        print(f"   r={r}: E_0/(2r-1)!!={lhs:.1f}  (n)_r={rhs}  <=? {ok}")
    print(f"   => binomial-EGF coeff-bound {'VIOLATED (conjecture FALSE)' if viol else 'holds'}")
print()
print("(L2)+(L3) W_r/slack_r ratio (the real open input) + slack growth, prize prime:")
for n,p in [(16,65537),(32,1048609)]:
    E=Er(p,n,7)
    print(f" n={n} p={p}:")
    print(f"   {'r':>2} {'W_r/slack_r':>11} {'slack/Wick':>10} {'~r^2/2n':>8} {'W_r/Wick':>9}")
    for r in range(2,8):
        wick=dfac(r)*n**r; E0=E0cf(r,n); Wr=E[r]-E0; slack=wick-E0
        wsl = Wr/slack if slack>0 else 0
        print(f"   {r:>2} {wsl:>11.4f} {slack/wick:>10.4f} {r*r/(2*n):>8.3f} {Wr/wick:>9.4f}")
print()
print("=> L2: if W_r/slack_r stays BOUNDED <1 -> prize favorable. If ->1 -> knife-edge/danger.")
print("   L3: slack/Wick ~ r^2/2n confirmed (the falling-factorial-derived slack size).")
