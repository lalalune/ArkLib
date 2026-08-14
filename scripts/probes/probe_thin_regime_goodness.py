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
        z=sum(mu[i] for i in x); s[(round(z.real,5),round(z.imag,5))]+=1
    return sum(c*c for c in s.values())
# THE decisive question: in the THIN regime beta=log p/log n >= 4 (where the prize lives, beta~5.3),
# is EVERY prime good (W_r/E_char0 small), or do sparse bad thin primes exist?
# goodness measure: W_r / E_char0  (wraparound as fraction of the char-0 signal). <1 = good.
print("THIN-regime goodness: W_r / E_char0 for ALL primes p==1 mod n with beta in [4, 5.5].")
print("(prize beta~5.3; if max ratio < 1 for ALL thin primes => uniformly good, no good-prime SELECTION needed)")
for n in [8,16]:
    ln=math.log(n)
    E0={r:E_char0(n,r) for r in [2,3]}
    lo=int(n**4); hi=int(n**5.5)
    print(f"\n n={n}: E_char0 r2={E0[2]} r3={E0[3]};  thin window [{lo},{hi}) (beta 4..5.5)")
    rows=[]; p=lo if lo%2 else lo+1
    while p<hi:
        if p%n==1 and isprime(p):
            mu=mu_Fp(n,p)
            beta=math.log(p)/ln
            w2=E_charP(mu,p,2)-E0[2]; w3=E_charP(mu,p,3)-E0[3]
            rows.append((p,beta,w2/E0[2],w3/E0[3],w2,w3))
        p+=2
        if len(rows)>=200: break
    if not rows:
        print("   (no primes in window)"); continue
    nz2=[r for r in rows if r[4]!=0]; nz3=[r for r in rows if r[5]!=0]
    maxr2=max(rows,key=lambda r:r[2]); maxr3=max(rows,key=lambda r:r[3])
    print(f"   #thin primes={len(rows)}; nonzero W_2: {len(nz2)}/{len(rows)}, nonzero W_3: {len(nz3)}/{len(rows)}")
    print(f"   max W_2/E0 = {maxr2[2]:.4f} at p={maxr2[0]} (beta={maxr2[1]:.2f})")
    print(f"   max W_3/E0 = {maxr3[2 if False else 3]:.4f} at p={maxr3[0]} (beta={maxr3[1]:.2f})")
    allgood = all(r[2]<1 and r[3]<1 for r in rows)
    print(f"   ALL thin primes good (W_r/E0 < 1 for r=2,3)? {'YES' if allgood else 'NO'}")
    # show any bad ones
    bad=[r for r in rows if r[2]>=1 or r[3]>=1]
    for r in bad[:6]:
        print(f"      BAD: p={r[0]} beta={r[1]:.2f} W2/E0={r[2]:.3f} W3/E0={r[3]:.3f}")
