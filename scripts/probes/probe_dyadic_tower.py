"""
2-power structure attack: the DYADIC TOWER. At a prime p = 1 mod 2n, both mu_n and mu_{2n} live in F_p
(mu_n = squares of mu_{2n}). Compute E_r and the wraparound for BOTH levels at the SAME p, look for a
multiplicative/tower relation W_r(2n) <-> W_r(n) (S3). Also: exact 2-adic valuation v_2(W_r) (which 2-power
symmetry group acts), and whether the dilation action (order n) divides W_r.
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
            return sorted(pow(h,i,p) for i in range(n))
def energies(p,S,R):
    c=Counter({0:1}); E={}
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc; E[r]=sum(m*m for m in c.values())
    return E
def v2(x):
    if x==0: return -1
    k=0
    while x%2==0: k+=1; x//=2
    return k
# char-0 closed forms for the wraparound reference (reliable r<=7)
def E0cf(r,n):
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n,
            6:10395*n**6-155925*n**5+1022175*n**4-3534300*n**3+6246471*n**2-4370520*n,
            7:135135*n**7-2837835*n**6+26801775*n**5-141891750*n**4+433726293*n**3-708996288*n**2+471556800*n}[r]

print("DYADIC TOWER: W_r(mu_n) and W_r(mu_{2n}) at the same prime p=1 mod 2n (reliable r<=7):")
for (n,p) in [(8, None),(16,None)]:
    twon=2*n
    p=twon+1
    while not(p%twon==1 and isprime(p) and p>twon**4//100): p+=1   # a prime with wraparound
    # pick a prime ~ (2n)^4 region so both levels have some wraparound
    p=twon**4+1
    while not(p%twon==1 and isprime(p)): p+=1
    Sn=subgroup(p,n); S2n=subgroup(p,twon)
    En=energies(p,Sn,7); E2n=energies(p,S2n,7)
    print(f" p={p}: levels n={n} and 2n={twon}")
    print(f"   {'r':>2} {'W_r(n)':>10} {'v2':>3} {'W_r(2n)':>12} {'v2':>3} {'W(2n)/W(n)':>10}")
    for r in range(2,8):
        Wn=En[r]-E0cf(r,n); W2n=E2n[r]-E0cf(r,twon)
        ratio = (W2n/Wn) if Wn else 0
        print(f"   {r:>2} {Wn:>10} {v2(Wn):>3} {W2n:>12} {v2(W2n):>3} {ratio:>10.2f}")
print()
print("READING: clean W(2n)/W(n) ratio or v2 pattern => a dyadic-tower recursion (S3, 2-power-specific).")
print("v2(W_r) = which 2-power group divides W_r (dilation n=2^mu => v2>=mu; bigger => more symmetry).")
