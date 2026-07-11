import itertools, cmath
from collections import Counter
def isprime(k):
    if k<2: return False
    i=2
    while i*i<=k:
        if k%i==0: return False
        i+=1
    return True
def v2(m):
    c=0
    while m%2==0: m//=2; c+=1
    return c
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
# Stratify W_r by v2(p-1).  n=2^a so v2(p-1)>=a is forced; "round/minimal" = v2 exactly a.
# Question: are minimal-v2 primes uniformly good (small W), and is W driven by EXCESS v2?
print("W_r stratified by v2(p-1).  n=2^a => v2>=a forced.  minimal v2 = a = 'round'.")
for n in [8,16]:
    a=v2(n)
    print(f"\n n={n} (a=v2(n)={a}), char0 ref:")
    E0={r:E_char0(n,r) for r in [2,3]}
    print(f"   E_char0: r2={E0[2]} r3={E0[3]}")
    print(f"   {'p':>7}{'v2(p-1)':>9}{'W_2':>8}{'W_3':>10}")
    cnt=0; p=n+1
    while cnt<26 and p < 60*n:
        if p%n==1 and isprime(p):
            mu=mu_Fp(n,p)
            w2=E_charP(mu,p,2)-E0[2]; w3=E_charP(mu,p,3)-E0[3]
            star='  <- minimal v2 (round)' if v2(p-1)==a else ''
            print(f"   {p:>7}{v2(p-1):>9}{w2:>8}{w3:>10}{star}")
            cnt+=1
        p+=1
