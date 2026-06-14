# 2-adic tower recursion test: eta^(mu)_b = T_b + T_{bg}.  Is the cross term non-amplifying?
# If B_mu^2 / B_{mu-1}^2 ~ 2 (clean), the recursion -> sqrt-growth = the bound (proof route).
# If cross term amplifies at some level, that localizes the obstruction.
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def v2(x):
    k=0
    while x%2==0: x//=2; k+=1
    return k
# find a prime with large 2-adic valuation of p-1 (for a deep tower), p ~ 10^6
MUMAX=13
p=None
cand = (1<<MUMAX)*70 + 1
while cand < 4_000_000:
    if isprime(cand) and v2(cand-1)>=MUMAX: p=cand; break
    cand += (1<<MUMAX)
print(f"p={p}, v2(p-1)={v2(p-1)}, building tower mu=1..{MUMAX}",flush=True)
g0=primroot(p)
# generator of the full 2^MUMAX subgroup:
gfull=pow(g0,(p-1)//(1<<MUMAX),p)
pe=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
def eta(b, sub):  # sum_{x in sub} e_p(b x)
    s=0j
    for x in sub: s+=pe[(b*x)%p]
    return s
prevB=None
print(f"{'mu':<4}{'n':<7}{'B_mu':<10}{'B^2/(n log p)':<15}{'B_mu^2/B_{mu-1}^2':<18}{'cross/|T|^2 @worst':<18}",flush=True)
for mu in range(1, MUMAX+1):
    n=1<<mu
    step=1<<(MUMAX-mu)
    g=pow(gfull, step, p)               # primitive 2^mu-th root
    sub=[pow(g,j,p) for j in range(n)]  # mu_{2^mu}
    subhalf=[pow(g,j,p) for j in range(n//2)] if mu>=1 else [1]  # mu_{2^{mu-1}}
    gg=pow(g,1,p)                       # coset rep: g itself (non-square)
    # B over cosets: eta constant on cosets of sub; reps = g0^i, i=0..(p-1)/n -1
    m=(p-1)//n
    bestB=0.0; bestb=1
    gi=1
    for i in range(m):
        val=abs(eta(gi, sub))
        if val>bestB: bestB=val; bestb=gi
        gi=gi*g0%p
    # decompose at worst b: eta = T_b + T_{b*g} over the half-subgroup
    if mu>=2:
        Tb=eta(bestb, subhalf); Tbg=eta((bestb*gg)%p, subhalf)
        cross=2*(Tb.conjugate()*Tbg).real
        denom=abs(Tb)**2+abs(Tbg)**2
        crossratio=cross/denom if denom>0 else 0
    else:
        crossratio=float('nan')
    ratio=bestB**2/prevB**2 if prevB else float('nan')
    print(f"{mu:<4}{n:<7}{bestB:<10.3f}{bestB**2/(n*math.log(p)):<15.4f}{ratio:<18.4f}{crossratio:<18.4f}",flush=True)
    prevB=bestB
