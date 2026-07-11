import itertools, cmath, math
from collections import Counter
def isprime(k):
    if k<2: return False
    i=2
    while i*i<=k:
        if k%i==0: return False
        i+=1
    return True
def thin_primes(n, lo, count):
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
# The prize quantity: mu_{2r} = (p*E_r - n^{2r})/(p-1) = DC-subtracted moment. Decompose:
#   p*E_r - n^{2r} = p*E0 + (p*W_r - n^{2r}),  W_r=E_r-E0.   'wrapcorr' := p*W_r - n^{2r}.
# Prize floor needs mu_{2r} <= Wick.  Equivalently DCmoment=(p*E_r-n^{2r}) <= (p-1)*Wick.
# KEY: is the wraparound correction (p*W_r-n^{2r}) negative/small (sub-random => HELPS)?
n=8
print(f"n={n}.  wrapcorr = p*W_r - n^(2r) (random-mean-subtracted wraparound; <0 = sub-random = HELPS)")
print(f"{'p':>8}{'beta':>6}{'r':>3}{'W_r':>12}{'rand n^2r/p':>13}{'wrapcorr':>14}{'wrapcorr/slack':>15}{'DCmom/(p-1)Wick':>17}")
for plo in [n**4, n**5]:
    for p in thin_primes(n, plo, 1):
        mu=mu_Fp(n,p); beta=math.log(p)/math.log(n)
        for r in range(2,7):
            E0=E_char0(n,r); Wick=dfact(r)*n**r
            Ep=E_charP(mu,p,r); W=Ep-E0
            rand=(n**(2*r))/p
            wrapcorr=p*W - n**(2*r)
            slack=Wick-E0
            DCmom=p*Ep - n**(2*r)
            ratio_wc = wrapcorr/slack if slack>0 else float('nan')
            ratio_dc = DCmom/((p-1)*Wick)
            print(f"{p:>8}{beta:>6.2f}{r:>3}{W:>12}{rand:>13.1f}{wrapcorr:>14}{ratio_wc:>15.3f}{ratio_dc:>17.4f}")
        print()
