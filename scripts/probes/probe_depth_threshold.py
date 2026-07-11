import itertools, math
from collections import Counter
def isprime(k):
    if k<2: return False
    if k%2==0: return k==2
    i=3
    while i*i<=k:
        if k%i==0: return False
        i+=2
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
def dfact(m):
    pr=1
    while m>0: pr*=m; m-=2
    return pr
# slack = (Wick - E_char0) + (n^2r - Wick)/p ; prize criterion rho_r<=1 <=> W_r<=slack (_RhoDecomposition).
# r_onset = (1/2) p^{1/phi(n)} : W_r=0 for r<r_onset (onset ceiling). saddle r~ln p.
def phi2(n):  # phi(2^a)=2^{a-1}
    a=0;m=n
    while m%2==0: m//=2;a+=1
    return 2**(a-1)
print("Does W_r<=slack hold across depths?  where is r_onset vs the saddle?  is the Minkowski count (2r)^phi/p tight?")
for n in [8,16]:
    phi=phi2(n)
    print(f"\n n={n} (phi(n)={phi}):")
    rmax = 8 if n==8 else 6
    # one representative thin prime per n
    p = 4129 if n==8 else 65537
    while not (isprime(p) and p%n==1): p+=1
    mu=mu_Fp(n,p)
    r_onset = 0.5 * p**(1.0/phi)
    saddle = math.log(p)
    print(f"   thin prime p={p}: r_onset=(1/2)p^(1/phi)={r_onset:.3f}, saddle=ln p={saddle:.2f}")
    print(f"   {'r':>3}{'E_char0':>14}{'W_r':>12}{'slack':>16}{'W_r/slack':>11}{'<=1?':>6}{'Mink (2r)^phi/p':>16}")
    E0cache={}
    import cmath
    def E_char0(n,r):
        mu0=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
        s=Counter()
        for x in itertools.product(range(n),repeat=r):
            z=sum(mu0[i] for i in x); s[(round(z.real,3),round(z.imag,3))]+=1
        return sum(c*c for c in s.values())
    for r in range(2,rmax+1):
        Wick=dfact(2*r-1)*n**r
        E0=E_char0(n,r)
        n2r=n**(2*r)
        Er=E_charP(mu,p,r)
        Wr=Er-E0
        slack=(Wick-E0)+(n2r-Wick)/p
        ratio=Wr/slack if slack>0 else float('nan')
        mink=(2*r)**phi/p
        ok='YES' if Wr<=slack else 'NO'
        print(f"   {r:>3}{E0:>14}{Wr:>12}{slack:>16.1f}{ratio:>11.5f}{ok:>6}{mink:>16.2e}")
print("\nPRIZE scale: phi(n)=2^29, p~2^158.  r_onset=(1/2)*2^(158/2^29)=(1/2)*2^(2.9e-7)~0.5 < 1.")
print("So NO integer depth r>=1 is below onset => the unconditional W=0 region is EMPTY at prize scale.")
print("Minkowski count (2r)^phi: at r=1, 2^(2^29) >> p=2^158, so the crude count bound is astronomically VACUOUS.")
