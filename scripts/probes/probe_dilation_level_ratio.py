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
        if p>target and p>n**3 and is_prime(p) and (p-1)//n>1: return p
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

# IDEA: TRANSFER OPERATOR FOR THE DILATION COCYCLE.
# eta_b = sum_{x in mu_n} e_p(bx). The 2-power tower: f_i(b)=sum_{x in mu_{2^i}} e_p(bx),
# f_{i+1}(b)=f_i(b)+f_i(zeta b). This is a 2-to-1 SUBSTITUTION/RENORMALIZATION:
# define the WEIGHTED transfer operator on functions of b: (L phi)(b) = e_p(b)*phi(b) summed
# over the doubling-map PREIMAGES. We test: does max|f_i| grow like a PRODUCT of operator norms
# (sub-multiplicative) or does the SPECTRAL RADIUS of the level-transfer matrix bound it below 2^i?
# Concretely: the m periods at level mu form a VECTOR; the level-doubling acts LINEARLY on the
# m-vector of periods of mu_{2^i} indexed by coset. We extract that m x m doubling matrix and
# look at its spectral radius vs the growth of max|eta|.

for (n,beta) in [(8,4),(16,4),(32,4)]:
    p=find_prime(n,beta); S,g=subgroup(p,n); m=(p-1)//n
    w=2j*math.pi/p
    # periods of full mu_n indexed by coset c: eta_c = sum_{x in mu_n} e_p(g^c x)
    eta=[sum(cmath.exp(w*((pow(g,c,p)*x)%p)) for x in S) for c in range(m)]
    M=max(abs(e) for e in eta)
    tgt=math.sqrt(n*math.log(p/n))
    # Now the half-subgroup mu_{n/2} = squares within mu_n. zeta = primitive 2nd-level elt = h^{?}
    # mu_{n/2} = <h^2>. f_half_c = sum_{x in mu_{n/2}} e_p(g^c x)
    h=pow(g,(p-1)//n,p)
    half=[pow(h,2*j,p) for j in range(n//2)]
    fh=[sum(cmath.exp(w*((pow(g,c,p)*x)%p)) for x in half) for c in range(m)]
    Mh=max(abs(e) for e in fh)
    # doubling check: eta_c = fh_c + fh_{c shifted by zeta}. zeta=h (shifts coset c by +1? since g^c*h=g^{c+1})
    # actually mu_n = mu_{n/2} cup h*mu_{n/2}; e_p(g^c h x)=fh at b=g^c h=g^{c+ (p-1)/n}... messy; test ratio
    print(f"n={n} p={p} m={m}: M={M:.3f} M/tgt={M/tgt:.3f} | M_half={Mh:.3f} ratio M/M_half={M/Mh:.3f} (free bd=2)")
