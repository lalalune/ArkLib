import itertools, cmath, math

def find_primes_with_n(n, count=3, start=3):
    # primes p with n | p-1
    res=[]; p=start
    def isprime(k):
        if k<2: return False
        i=2
        while i*i<=k:
            if k%i==0: return False
            i+=1
        return True
    p = n+1
    while len(res)<count:
        if p%n==1 and isprime(p): res.append(p)
        p+=1
    return res

def mu_n_Fp(n,p):
    # n-th roots of unity in F_p: g^{(p-1)/n * k}
    # find a generator g of F_p^*
    def order(a,p):
        o=1; x=a%p
        while x!=1:
            x=(x*a)%p; o+=1
        return o
    g=2
    while order(g,p)!=p-1: g+=1
    h=pow(g,(p-1)//n,p)  # primitive n-th root
    return [pow(h,k,p) for k in range(n)]

def mu_n_C(n):
    return [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]

def energy_charP(n,p,r):
    mu=mu_n_Fp(n,p)
    # count tuples x,y in mu^r with sum x = sum y mod p; via rep counts of r-fold sums
    from collections import Counter
    sums=Counter()
    for x in itertools.product(mu,repeat=r):
        sums[sum(x)%p]+=1
    return sum(c*c for c in sums.values())

def energy_char0(n,r):
    # count tuples x,y in mu_n(C)^r with sum x = sum y exactly (complex); via rep counts, round
    from collections import Counter
    mu=mu_n_C(n)
    sums=Counter()
    for x in itertools.product(range(n),repeat=r):
        s=sum(mu[i] for i in x)
        key=(round(s.real,6),round(s.imag,6))
        sums[key]+=1
    return sum(c*c for c in sums.values())

def doublefact(k):  # (2r-1)!!
    res=1
    for j in range(1,k+1): res*=(2*j-1)
    return res

print(f"{'n':>4}{'r':>3}{'p':>8} {'E_charP':>12}{'E_char0':>12}{'W_r=Ep-E0':>12}{'Wick=(2r-1)!!n^r':>18}{'slack=Wick-E0':>14}{'W/slack':>9}{'W/sqrt(offdiag)':>16}")
for n in [8,16]:
    for r in [2,3,4]:
        E0=energy_char0(n,r)
        Wick=doublefact(r)*(n**r)
        slack=Wick-E0
        ps=find_primes_with_n(n,3, start=max(3, 4*n*n))  # thin-ish: p > n^2 (no/less wraparound)
        for p in ps:
            Ep=energy_charP(n,p,r)
            W=Ep-E0
            offdiag_count=(n**(2*r))-E0  # rough off-diagonal population
            ratio_slack = W/slack if slack>0 else float('nan')
            ratio_sqrt = W/math.sqrt(offdiag_count) if offdiag_count>0 else float('nan')
            print(f"{n:>4}{r:>3}{p:>8} {Ep:>12}{E0:>12}{W:>12}{Wick:>18}{slack:>14}{ratio_slack:>9.3f}{ratio_sqrt:>16.3f}")
