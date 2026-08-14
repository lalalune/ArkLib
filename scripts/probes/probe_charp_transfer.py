"""
Attack the char-p transfer G_p(r)>=0 via G_p = G_0 + L(W) + Q(W):
  E_r(F_p)=E_r^0+W_r;  G(r)=(2r+3)E_{r+1}^2-(2r+1)E_r E_{r+2}.
  G_p = G_0 + L + Q,
  L = 2(2r+3)E_{r+1}^0 W_{r+1} - (2r+1)(E_r^0 W_{r+2} + E_{r+2}^0 W_r)   [linear in W]
  Q = (2r+3)W_{r+1}^2 - (2r+1)W_r W_{r+2}                                [wraparound's own log-convexity gap]
Check: signs of G_0, L, Q; is L+Q>=0? does G_0 dominate -(L+Q)? Also the wraparound recursion
  W_{r+1} = n W_r + Dcross_r.  And the margin slack_r=Wick_r-E_r^0 vs W_r.
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
def energies(p,n,R):
    S=subgroup(p,n); c=Counter({0:1}); E={}
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc
        E[r]=sum(m*m for m in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
n=16; R=12
q=10**9
while not(q%n==1 and isprime(q)): q+=1
E0=energies(q,n,R)
print(f"n={n}. char-p transfer decomposition G_p=G_0+L+Q at prize primes:")
for p in [65537, 65617, 70001]:
    while not(p%n==1 and isprime(p)): p+=1
    Ep=energies(p,n,R)
    W={r:Ep[r]-E0[r] for r in range(1,R+1)}
    print(f" p={p}:")
    print(f"   {'r':>2} {'G_0':>10} {'L':>10} {'Q':>10} {'L+Q':>10} {'G_p':>10} {'G_p>=0':>7} {'W_r/slack':>9}")
    for r in range(2,R-1):
        G0=(2*r+3)*E0[r+1]**2-(2*r+1)*E0[r]*E0[r+2]
        L=2*(2*r+3)*E0[r+1]*W[r+1]-(2*r+1)*(E0[r]*W[r+2]+E0[r+2]*W[r])
        Q=(2*r+3)*W[r+1]**2-(2*r+1)*W[r]*W[r+2]
        Gp=(2*r+3)*Ep[r+1]**2-(2*r+1)*Ep[r]*Ep[r+2]
        slack=dfac(r)*n**r - E0[r]
        wsl = W[r]/slack if slack>0 else 0
        # signs (sci notation magnitude)
        def sg(x): return f"{x:+.1e}"
        print(f"   {r:>2} {sg(G0):>10} {sg(L):>10} {sg(Q):>10} {sg(L+Q):>10} {sg(Gp):>10} {str(Gp>=0):>7} {wsl:>9.4f}")
