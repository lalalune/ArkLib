import itertools, math

def primitive_root(p):
    # find a generator of F_p^*
    if p==2: return 1
    phi=p-1
    # factor phi
    fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def isprime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True

def mun(n,p):
    g=primitive_root(p)
    b=pow(g,(p-1)//n,p)
    return [pow(b,i,p) for i in range(n)]

def count_e2(n,p,w):
    """Count w-subsets S of mu_n with e1(S)!=0 and e2(S)=0 (i.e. e1^2 = p2).
       Return (raw count, #distinct e1 values, K=#dilation-orbits of e1 under mu_n)."""
    mu=mun(n,p)
    e1vals=[]
    cnt=0
    for S in itertools.combinations(mu,w):
        e1=sum(S)%p
        if e1==0: continue
        p2=sum((x*x)%p for x in S)%p
        if (e1*e1-p2)%p==0:
            cnt+=1; e1vals.append(e1)
    rem=set(e1vals); K=0
    while rem:
        x=next(iter(rem))
        rem-=set((u*x)%p for u in mu)
        K+=1
    return cnt, len(set(e1vals)), K

def find_prize_prime(n, lo):
    # smallest prime p>=lo with n | p-1, in "prize-ish" regime q>=n^3
    p=lo
    while True:
        if (p-1)%n==0 and isprime(p): return p
        p+=1

# R4 conjecture: for fixed width w, K = O(1) (probe claims w=5 -> 1)
# Validate in PRIZE regime: q >= n^3, proper subgroup mu_n (not full group)
print("=== R4 e2=0 coset count: K(orbit count of e1) by (n, w), prize regime q>=n^3 ===")
for n in [8,12,16,20,24]:
    p=find_prize_prime(n, n**3)
    for w in [4,5,6]:
        if w>n: continue
        try:
            cnt,dist,K=count_e2(n,p,w)
            print(f"  n={n:2d} p={p:7d} (q/n^3={p/n**3:.1f}) w={w}: raw={cnt:6d} #distinct_e1={dist:5d} K={K}")
        except Exception as e:
            print(f"  n={n} w={w} ERR {e}")
