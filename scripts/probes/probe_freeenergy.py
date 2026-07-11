import cmath, math
def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def find_prime(n, beta):
    target=int(n**beta); k=max(1,(target-1)//n)
    while True:
        p=1+k*n
        if p>target and is_prime(p) and (p-1)//n>1: return p
        k+=1
def gen(p):
    fac=[]; x=p-1; d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def subgroup(p,n):
    g=gen(p); h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    return S,g

# IDEA: the SCALED CUMULANT GENERATING FUNCTION (free energy) of the period family.
# Lambda(t) = (1/?) log E_c[exp(t |eta_c|^2 / n)] -- its Legendre transform IS the rate I(x).
# If Lambda is FINITE and STRICTLY CONVEX up to t->infty edge, get effective LDP -> sup bound.
# Test: is the empirical MGF of |eta|^2/n sub-exponential? And the key: SECOND CUMULANT vs higher.
for (n,beta) in [(8,5),(16,4),(32,4)]:
    p=find_prime(n,beta); S,g=subgroup(p,n); m=(p-1)//n
    Y=[]  # |eta_c|^2 / n  ; mean should be ~ (p-n)/(m) /n ~ 1 (Parseval: sum |eta|^2 = (p-1) - (n-1)*? )
    for c in range(m):
        b=pow(g,c,p)
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        Y.append((abs(s)**2)/n)
    mean=sum(Y)/m
    var=sum((y-mean)**2 for y in Y)/m
    # third/fourth standardized
    sd=math.sqrt(var)
    skew=sum((y-mean)**3 for y in Y)/m/sd**3
    kurt=sum((y-mean)**4 for y in Y)/m/sd**4
    Mn=max(Y)  # = M^2/n
    print(f"n={n} p={p} m={m}: E[|eta|^2/n]={mean:.3f} Var={var:.3f} skew={skew:.2f} exKurt={kurt-3:.2f} max(|eta|^2/n)={Mn:.3f}")
    # For an EXPONENTIAL(rate 1) distribution (which |eta/sqrt(n)|^2 ~ if eta gaussian): mean=var=1, skew=2, kurt=9.
    # measure deviation from exponential => sub/super exponential tail
