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
def onset_r0(n,p,rmax):
    E0={r:E_char0(n,r) for r in range(1,rmax+1)}
    mu=mu_Fp(n,p)
    for r in range(1,rmax+1):
        if E_charP(mu,p,r)-E0[r] != 0:
            return r
    return None  # > rmax
# n=4 (phi=2): r0 ~ p^{1/2}?  n=8 (phi=4): r0 ~ p^{1/4}?
print("onset r_0(n,p) vs the norm-bound order p^{1/phi(n)} and log p:")
for n,rmax,phi in [(4,11,2),(8,8,4)]:
    print(f"\n--- n={n} (phi={phi}), norm order p^(1/{phi}) ---")
    print(f"{'p':>9}{'beta=lnp/lnn':>14}{'r_0':>6}{'p^(1/phi)':>11}{'log_n p':>9}{'r_0/p^(1/phi)':>14}")
    cnt=0; p=n+1
    while cnt<8:
        if p%n==1 and isprime(p):
            r0=onset_r0(n,p,rmax)
            beta=math.log(p)/math.log(n)
            nb=p**(1.0/phi)
            r0s=str(r0) if r0 else f">{rmax}"
            ratio = (r0/nb) if r0 else float('nan')
            print(f"{p:>9}{beta:>14.2f}{r0s:>6}{nb:>11.2f}{beta:>9.2f}{ratio:>14.3f}")
            cnt+=1
            p += max(1, p//3)  # spread p geometrically
        p+=1
