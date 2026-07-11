import itertools, cmath, math
from collections import Counter
def isprime(k):
    if k<2: return False
    i=2
    while i*i<=k:
        if k%i==0: return False
        i+=1
    return True
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
# The capstone's hypothesis: Var_P(W_r) <= E_P[W_r] (sub-Poisson) over the prime family.
# W_r(p) = E_charP - E_char0 = the wraparound count. Family = primes p==1 mod n in a window.
print("Sub-Poisson check: is Var_P(W_r) <= mean_P(W_r) over the prime family?")
print(f"{'n':>3}{'r':>3}{'window':>16}{'#primes':>8}{'mean(W)':>12}{'var(W)':>14}{'var/mean':>10}{'subPoisson?':>12}")
for n in [4,8]:
    E0={r:E_char0(n,r) for r in range(2,5)}
    for r in [2,3,4]:
        for (lo,hi) in [(n,4*n*n),(4*n*n,16*n*n)]:  # thick window and thinner window
            Ws=[]
            p=lo
            while p<hi and len(Ws)<40:
                if p%n==1 and isprime(p):
                    mu=mu_Fp(n,p); Ws.append(E_charP(mu,p,r)-E0[r])
                p+=1
            if len(Ws)<3: continue
            mean=sum(Ws)/len(Ws)
            var=sum((w-mean)**2 for w in Ws)/len(Ws)
            ratio=var/mean if mean>0 else float('nan')
            sp = 'YES' if (mean<=0 or var<=mean) else 'NO'
            print(f"{n:>3}{r:>3}{f'[{lo},{hi})':>16}{len(Ws):>8}{mean:>12.1f}{var:>14.1f}{ratio:>10.2f}{sp:>12}")
