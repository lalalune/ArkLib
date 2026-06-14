import itertools
# q-independent: for direction (a,b) and agreement subset T of mu_n (exponent set), 
# bad gamma exists iff X^a+gamma X^b reduces to deg<k mod m_T for some gamma.
# Work over a large clean prime to represent Z[zeta] faithfully (p huge => no spurious).
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n: return [pow(g,i,p) for i in range(n)]
def polymod(coeffs, m, p):
    # reduce poly (list, low->high) modulo monic m (list low->high, deg = len-1)
    c=coeffs[:]; dm=len(m)-1
    for i in range(len(c)-1, dm-1, -1):
        if c[i]:
            f=c[i]
            for j in range(dm+1):
                c[i-dm+j]=(c[i-dm+j]-f*m[j])%p
    return c[:dm]
def m_of_T(T,p):
    # monic poly with roots T
    poly=[1]
    for r in T:
        new=[0]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]=(new[i]+c*(-r))%p
            new[i+1]=(new[i+1]+c)%p
        poly=new
    return poly
def bad_gammas(p,H,a,b,k,t):
    n=len(H); res=set()
    for sub in itertools.combinations(range(n),t):
        T=[H[i] for i in sub]
        if len(set(T))!=t: continue
        m=m_of_T(T,p)
        Xa=[0]*(a+1); Xa[a]=1; ra=polymod(Xa,m,p)
        Xb=[0]*(b+1); Xb[b]=1; rb=polymod(Xb,m,p)
        # need ra + gamma rb to have coeffs[k..t-1] = 0  => for each j in k..t-1: ra[j]+gamma rb[j]=0
        # solve for gamma consistent across all j
        gamma=None; ok=True
        for j in range(k, t):
            A=ra[j] if j<len(ra) else 0
            B=rb[j] if j<len(rb) else 0
            if B==0:
                if A!=0: ok=False;break
            else:
                g=(-A*pow(B,p-2,p))%p
                if gamma is None: gamma=g
                elif gamma!=g: ok=False;break
        if ok and gamma is not None and gamma!=0:
            res.add(gamma)
    return res
n=16; k=8; p=find_prime(n, 2000)  # large-ish clean prime, fewer spurious
H=subgroup(p,n)
print(f"n={n} k={k} (ρ=0.5) p={p}: q-indep bad-scalar counts per direction(a,b), agreement t")
print(f"{'dir':>8} {'t':>3} {'δ=1-t/n':>8} {'#bad':>6}")
for (a,b) in [(9,10),(9,11),(10,11),(9,13),(11,13),(10,12),(9,15)]:
    for t in [b, b-1, b+1]:
        if t<=k or t>n: continue
        bg=bad_gammas(p,H,a,b,k,t)
        if bg: print(f"  ({a},{b}) {t:>3} {1-t/n:>8.3f} {len(bg):>6}", flush=True)
