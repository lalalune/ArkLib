"""#389 DECISIVE: smooth dyadic-domain coset-union construction -> exponential supply.
A union A of cosets of mu_d (d=2^j) in mu_n has prod_{a in A}(X-a) a polynomial in X^d,
so e_1(A)=...=e_{d-1}(A)=0. If d>=m+2, every size-t coset-union is an explainable t-core
(forced poly W - W_t*prod_A has degree <= t-d = k-1 < k). Count = C(n/d, t/d) = exponential.
Verify by FULL enumeration that (a) coset-unions have e_1..e_{m+1}=0, (b) the (0,..,0) fiber
size, and (c) the forced-poly degree < k, hence supply >= C(n/d, t/d)."""
import itertools
from math import comb
from collections import defaultdict

def is_prime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True

def prime_factors(n):
    f=set();d=2
    while d*d<=n:
        while n%d==0: f.add(d);n//=d
        d+=1
    if n>1: f.add(n)
    return f

def mu(q,n):
    assert (q-1)%n==0
    for a in range(2,q):
        h=pow(a,(q-1)//n,q)
        if all(pow(h,n//p,q)!=1 for p in prime_factors(n)):
            return [pow(h,i,q) for i in range(n)], h
    return None,None

def esymm(A,q,upto):
    e=[1]+[0]*upto
    for a in A:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+a*e[i-1])%q
    return tuple(e[1:upto+1])

def polymul_modq(p,a,q):
    # multiply p (low..high) by (X - a)
    r=[0]*(len(p)+1)
    for i,c in enumerate(p):
        r[i]=(r[i]-a*c)%q
        r[i+1]=(r[i+1]+c)%q
    return r

def forced_deg(A,q,k,m,wt,c0):
    # W = wt*X^t + c0(deg<k);  forced = W - wt*prod_A ; return its degree
    t=k+m+1
    prodA=[1]
    for a in A: prodA=polymul_modq(prodA,a,q)  # degree t monic
    # W coeffs
    W=[0]*(t+1); W[t]=wt
    for j,cc in enumerate(c0): W[j]=(W[j]+cc)%q
    forced=[(W[j]-wt*prodA[j])%q for j in range(t+1)]
    d=t
    while d>=0 and forced[d]%q==0: d-=1
    return d

def run():
    print("=== Verify coset-union -> e_1..e_{d-1}=0 and supply >= C(n/d,t/d) ===\n")
    cases=[(17,16,4),(97,16,4),(97,32,4),(193,32,4),(97,16,2),(97,16,8)]
    for (q,n,d) in cases:
        if (q-1)%n: continue
        sub,h=mu(q,n)
        if sub is None: continue
        # subgroup mu_d = {x^{n/d}} = powers of h^{n/d}
        gd=pow(h,n//d,q)
        mud=[pow(gd,i,q) for i in range(d)]
        # cosets of mu_d in mu_n: reps = h^i for i in 0..n/d-1
        ncos=n//d
        cosets=[[ (pow(h,r,q)*x)%q for x in mud] for r in range(ncos)]
        # pick m = d-2 (so m+1=d-1, need e_1..e_{m+1}=0 <= e_1..e_{d-1}=0)
        m=d-2
        # take s cosets, t=s*d ; need t=k+m+1 => k=t-m-1 ; pick s
        for s in [2, ncos//2 if ncos>=4 else 2]:
            if s<1 or s>ncos: continue
            t=s*d; k=t-m-1
            if k<1: continue
            # verify: each union of s cosets has e_1..e_{m+1}=0 and forced deg<k
            import random; rng=random.Random(1)
            wt=3; c0=[rng.randrange(q) for _ in range(k)]
            allzero=True; alldeg=True; cnt=0
            sample=list(itertools.combinations(range(ncos), s))
            for combo in sample[:300]:  # sample if too many
                A=[]
                for r in combo: A+=cosets[r]
                e=esymm(A,q,m+1)
                if any(x!=0 for x in e): allzero=False
                fd=forced_deg(A,q,k,m,wt,c0)
                if not (fd<k): alldeg=False
                cnt+=1
            total=comb(ncos,s)
            johnson = (k*n)**0.5
            print(f"q={q} n={n} d={d} m={m} s={s} t={t} k={k} rate={k/n:.3f} alpha={t/n:.3f} sqrt_rho={ (k/n)**0.5:.3f}: "
                  f"e_zero={allzero} deg<k={alldeg} supply>=C({ncos},{s})={total}  (linear n={n})")
    print("\n=== FULL ENUMERATION on mu_16: max (e_1..e_{m+1}) fiber vs coset-union count ===")
    q,n=97,16
    sub,h=mu(q,n)
    for d in [4]:
        m=d-2; 
        for s in [2]:
            t=s*d; k=t-m-1; ncos=n//d
            fib=defaultdict(int)
            for A in itertools.combinations(sub,t):
                fib[esymm(A,q,m+1)]+=1
            mx=max(fib.values()); zero=fib[tuple([0]*(m+1))]
            print(f"d={d} m={m} t={t} k={k}: MAX fiber={mx}, (0..0)fiber={zero}, coset-union C({ncos},{s})={comb(ncos,s)}, linear={n}")

if __name__=="__main__": run()
