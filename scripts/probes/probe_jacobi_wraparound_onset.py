import itertools, cmath, math
from collections import Counter
def isprime(k):
    if k<2: return False
    i=2
    while i*i<=k:
        if k%i==0: return False
        i+=1
    return True
def thin_primes(n, lo, count=2):
    res=[]; p=lo
    while len(res)<count:
        if p%n==1 and isprime(p): res.append(p)
        p+=1
    return res
def mu_Fp(n,p):
    def order(a,p):
        o=1;x=a%p
        while x!=1: x=(x*a)%p;o+=1
        return o
    g=2
    while order(g,p)!=p-1: g+=1
    h=pow(g,(p-1)//n,p)
    return [pow(h,k,p) for k in range(n)]
def E_charP(mu,p,r):
    s=Counter()
    for x in itertools.product(mu,repeat=r): s[sum(x)%p]+=1
    return sum(c*c for c in s.values())
def E_char0(n,r):
    mu=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
    s=Counter()
    for x in itertools.product(range(n),repeat=r):
        z=sum(mu[i] for i in x); s[(round(z.real,5),round(z.imag,5))]+=1
    return sum(c*c for c in s.values())
def dfact(r):
    res=1
    for j in range(1,r+1): res*=(2*j-1)
    return res
# n=8 thin: p around n^3=512, n^3.5, n^4=4096, n^4.5 ; r up to 6
n=8
print(f"n={n}, n^2={n*n}, n^3={n**3}, n^4={n**4}.  Prize beta~5.27 => want p~n^5={n**5}")
print(f"{'p':>8}{'beta':>6}{'r':>3}{'W_r/slack':>11}{'cross?':>7}")
for plo in [n**3, n**4, n**5]:
    for p in thin_primes(n, plo, 1):
        mu=mu_Fp(n,p); beta=math.log(p)/math.log(n)
        for r in range(2,7):
            E0=E_char0(n,r); Wick=dfact(r)*n**r; slack=Wick-E0
            W=E_charP(mu,p,r)-E0
            rat=W/slack if slack>0 else float('nan')
            print(f"{p:>8}{beta:>6.2f}{r:>3}{rat:>11.4f}{'  FAIL' if rat>1 else '   ok':>7}")
        print()
