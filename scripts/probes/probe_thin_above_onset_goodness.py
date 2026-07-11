import itertools, cmath, math
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
def E_char0(n,r):
    mu=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
    s=Counter()
    for x in itertools.product(range(n),repeat=r):
        z=sum(mu[i] for i in x); s[(round(z.real,4),round(z.imag,4))]+=1
    return sum(c*c for c in s.values())
# n=16: onset r0 ~ p^{1/8}.  For p in [65536, 16^5=1048576], r0 ~ 4..5.6.
# r=5 is ABOVE onset for p up to ~16^5, AND beta=log p/log16 in [4,5]. THE informative computable window.
n=16; ln=math.log(n)
print(f"n={n}: testing r=5 (ABOVE onset r0~4) in THIN window beta in [4,5].")
print("If max W_5/E0 stays <1 across all thin primes => uniformly good ABOVE onset (genuine prize-relevant signal).")
for r in [5]:
    E0=E_char0(n,r)
    lo,hi=65536, 16**5
    print(f"\n r={r}: E_char0={E0}, window [{lo},{hi})")
    rows=[]; p=lo+1
    while p<hi and len(rows)<24:
        if p%n==1 and isprime(p):
            mu=mu_Fp(n,p)
            beta=math.log(p)/ln; r0=p**(1/8)
            w=E_charP(mu,p,r)-E0
            rows.append((p,beta,r0,w/E0,w))
        p+=2
    for (p,beta,r0,ratio,w) in rows:
        flag=' ABOVE-onset' if r>r0 else ' below-onset'
        bad=' <<< BAD (>1)' if ratio>=1 else ''
        print(f"   p={p:>9} beta={beta:.2f} r0={r0:.1f}{flag}  W_5/E0={ratio:+.5f}  W_5={w}{bad}")
    above=[x for x in rows if r>x[2]]
    if above:
        mx=max(above,key=lambda x:abs(x[3]))
        allgood=all(x[3]<1 for x in above)
        print(f"\n   ABOVE-onset primes: {len(above)}; max |W_5/E0|={abs(mx[3]):.5f} at p={mx[0]}; nonzero W: {sum(1 for x in above if x[4]!=0)}")
        print(f"   ALL above-onset thin primes good (W_5/E0<1)? {'YES' if allgood else 'NO'}")
