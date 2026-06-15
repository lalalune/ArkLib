# Route 36 decisive test: are deep holes the CONCENTRATION points (max #bad-gamma), or anti-concentration?
# concentration of a pencil (u0,u1): #bad-gamma(delta) = #{gamma : u0+gamma*u1 is (1-delta)-agreeing with RS[k]}.
# We computed deep holes = monomials x^j with j == k mod 4 (agree=k, MINIMAL). Now compute, for monomial
# pencils (x^a, x^b), the #bad-gamma at the binding radius, and check whether the WORST pencil uses
# deep-hole exponents or the high-agreement (x^{n/2}-family) exponents.
import itertools, math
from sympy import primitive_root, isprime
def setup(n,beta=4):
    p=n**beta
    while not ((p-1)%n==0 and isprime(p)): p+=1
    g=pow(primitive_root(p),(p-1)//n,p); mu=[pow(g,j,p) for j in range(n)]
    return p,mu
def agree_of_codeword_on_subset(u,mu,k,p,smin):
    """max agreement of u with deg<k poly. (returns max agreement over all k-subset interpolations)"""
    n=len(mu); best=0
    for T in itertools.combinations(range(n),k):
        ag=0
        for xi in range(n):
            x=mu[xi]; val=0
            for i in T:
                num=1;den=1
                for j in T:
                    if i!=j: num=num*((x-mu[j])%p)%p; den=den*((mu[i]-mu[j])%p)%p
                val=(val+u[i]*num*pow(den,p-2,p))%p
            if val==u[xi]: ag+=1
        best=max(best,ag)
    return best
def nbad_pencil(a,b,mu,k,p,smin):
    """#{gamma in F_p* : x^a + gamma*x^b agrees with some deg<k poly on >= smin points}."""
    n=len(mu); ua=[pow(mu[i],a,p) for i in range(n)]; ub=[pow(mu[i],b,p) for i in range(n)]
    # for each (k+1)-subset, the agreement forces a unique gamma (over-det); collect gammas with agree>=smin
    cand=set()
    for T in itertools.combinations(range(n),k+1):
        # solve for gamma s.t. ua+gamma*ub interpolates deg<k on T (k+1 pts, deg<k => 1 constraint)
        # divided diff of order k of (ua+gamma*ub) over T = 0 => linear in gamma
        def ddk(u):
            t=0
            for i in T:
                den=1
                for j in T:
                    if i!=j: den=den*((mu[i]-mu[j])%p)%p
                t=(t+u[i]*pow(den,p-2,p))%p
            return t
        ea=ddk(ua); eb=ddk(ub)
        if eb%p==0: continue
        gam=(-ea*pow(eb,p-2,p))%p
        if gam!=0: cand.add(gam)
    # for each candidate gamma, compute true agreement, keep if >= smin
    good=set()
    for gam in cand:
        u=[(ua[i]+gam*ub[i])%p for i in range(n)]
        ag=agree_of_codeword_on_subset(u,mu,k,p,smin)
        if ag>=smin: good.add(gam)
    return len(good)
def main():
    n=16;k=3;p,mu=setup(n)
    print(f"=== n={n} k={k} p={p}: deep holes = exps j==k mod4 (agree=k=MINIMAL). Concentration test ===")
    deep=[3,7,11,15]; high=[8,9,10]  # high-agreement (non-deep) exps from prior probe (agree=4) + x^{n/2 family}
    smin=k+1  # just above interpolation
    print(f"  testing pencils, smin={smin} (agreement threshold):")
    best=(-1,None)
    for a in range(k,n):
        for b in range(k,n):
            if a>=b: continue
            nb=nbad_pencil(a,b,mu,k,p,smin)
            tag=""
            if a in deep or b in deep: tag+="[deep-hole exp]"
            print(f"    pencil(x^{a},x^{b}) gcd(b-a,n)={math.gcd(b-a,n)}: #bad-gamma(agree>={smin})={nb} {tag}")
            if nb>best[0]: best=(nb,(a,b))
    print(f"  WORST pencil = {best[1]} #bad={best[0]}; uses deep-hole exp? {best[1][0] in deep or best[1][1] in deep}")
if __name__=="__main__": main()
