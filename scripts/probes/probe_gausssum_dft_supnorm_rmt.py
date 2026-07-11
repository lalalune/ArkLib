import numpy as np, sympy
def setup(mu, beta=4.2):
    n=2**mu; m0=int(n**beta)//n
    if m0%2==0: m0+=1
    for dm in range(0,400000,2):
        for m in (m0+dm,m0-dm):
            if m<1: continue
            p=m*n+1
            if p>n**3 and sympy.isprime(p): return n,p,m
    raise RuntimeError
# use small mu so p-1 enumeration is cheap (mu=3, beta ~3.5 to keep p small but >n^3)
for mu,beta in [(3,3.6),(4,3.3)]:
    n,p,m=setup(mu,beta)
    g=sympy.primitive_root(p)
    a=np.arange(p-1)
    gpows=np.array([pow(int(g),int(x),p) for x in a],dtype=np.int64)
    ep=np.exp(2j*np.pi*gpows/p)
    T=np.arange(m)
    # Gauss sums G(chi_t), chi_t(g^a)=exp(2pi i t a/m)
    # G[t]=sum_a exp(2pi i t a/m) ep[a]
    PH=np.exp(2j*np.pi*np.outer(T,a)/m)   # m x (p-1)
    Gs=PH@ep
    recon=(n/(p-1))*(np.exp(-2j*np.pi*np.outer(np.arange(m),T)/m)@Gs)
    H=np.array([pow(int(g),(m*j)%(p-1),p) for j in range(n)])
    direct=np.array([np.sum(np.exp(2j*np.pi*((pow(int(g),i,p)*H)%p)/p)) for i in range(m)])
    err=np.max(np.abs(recon-direct))
    aj=Gs/np.sqrt(p)  # normalized, should be unimodular for t!=0
    print(f"mu={mu} n={n} p={p} m={m} beta={np.log(p)/np.log(n):.2f}")
    print(f"  recon err = {err:.2e}  => eta_vec = (n/(p-1)) * IDFT_m( G(chi_t) )  [CONFIRMED]")
    print(f"  |a_t|=|G/sqrt p| for t!=0: min={np.abs(aj[1:]).min():.4f} max={np.abs(aj[1:]).max():.4f} (=1 unimodular)")
    M=np.abs(direct).max()
    print(f"  M={M:.3f}  normalization (n/(p-1))*sqrt p = {n*np.sqrt(p)/(p-1):.4f}  sqrt(n)={np.sqrt(n):.3f}")
    # so eta = (sqrt p * n/(p-1)) * DFT of unimodular a_t. peak of DFT of m unimodulars ~ sqrt(m log m)*scale
    sc=np.sqrt(p)*n/(p-1)
    print(f"  M/scale = {M/sc:.3f}  vs sqrt(m log m)={np.sqrt(m*np.log(m)):.3f}  (=> DFT-supnorm of unimodular seq)")
    print(f"  CHECK M ~ scale*sqrt(m log m)= {sc*np.sqrt(m*np.log(m)):.3f}; and scale*sqrt(m)={sc*np.sqrt(m):.3f}=sqrt(n)*? ")
