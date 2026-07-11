import cmath, math
def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def find_prime(n, beta):
    target = int(n**beta)
    k = max(1, (target-1)//n)
    while True:
        p = 1 + k*n
        if p > target and is_prime(p) and (p-1)//n > 1:
            return p
        k += 1
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

# KEY IDEA TO PROBE: the period eta_b as a function of c (the coset index of b in F_p^* / mu_n).
# eta_c = sum_{x in mu_n} e_p(g^c x). The dilation b -> g b shifts c -> c+1 (a ROTATION of the m periods).
# The map c -> 2c mod m is the "doubling" induced by... no. Let's check: which arithmetic on c
# corresponds to a CONTRACTION of |eta|? Specifically test the renormalization
# eta over the index set, and whether the SET {c : |eta_c| large} is invariant under an explicit map.

for (n,beta) in [(8,4),(16,4)]:
    p=find_prime(n,beta); S,g=subgroup(p,n); m=(p-1)//n
    # periods indexed by c=0..m-1: b = g^c
    etas=[]
    for c in range(m):
        b=pow(g,c,p)
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        etas.append(s)
    mags=[abs(e) for e in etas]
    M=max(mags); cstar=mags.index(M)
    # Is the value eta_c real? (n even => -1 in mu_n => real). check
    maxim = max(abs(e.imag) for e in etas)
    # The doubling structure: since mu_n = <h>, multiply b by h gives same period. The relevant
    # "dynamics" on c: c -> c + m/?? Test: is the index of the worst period preserved under c->2c mod m?
    # Actually the genuine 2-adic dynamics: m = (p-1)/n. The Frobenius / multiply-by-(small prime) on b.
    # Probe: distribution of mags, and the LARGE DEVIATION count #{c: |eta_c| > x sqrt(n)}
    import statistics
    sn=math.sqrt(n)
    xs=[1.5,2.0,2.5,3.0]
    counts={x: sum(1 for v in mags if v> x*sn) for x in xs}
    # rate function check: -log(count/m)/x^2 should be ~1/2 if Gaussian LDP
    print(f"n={n} p={p} m={m} M/sqrt(n)={M/sn:.3f} maxImag={maxim:.2e} cstar={cstar}")
    for x in xs:
        cnt=counts[x]
        if cnt>0:
            rate = -math.log(cnt/m)/(x*x)
            print(f"   x={x}: #{{|eta|>{x}sqrt(n)}}={cnt}/{m} empirical rate I(x)/x^2={rate:.3f} (Gaussian=0.5)")
