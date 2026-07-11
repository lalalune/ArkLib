import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ntlib_pg import isprime, primitive_root
import numpy as np, math

def find_primes(n, beta=4, count=2):
    target=int(round(n**beta)); out=[]
    k=target-(target%n)+1
    while len(out)<count and k<target*6:
        if k>1 and isprime(k) and (k-1)%n==0: out.append(k)
        k+=n
    return out

def setup(p,n):
    g=primitive_root(p); m=(p-1)//n
    # discrete log table: dlog[g^k]=k
    dlog=np.zeros(p,dtype=np.int64); x=1
    for k in range(p-1):
        dlog[x]=k; x=x*g%p
    w=np.exp(2j*np.pi/p)
    return g,m,dlog,w

def periods(p,n,w):
    g=primitive_root(p); m=(p-1)//n
    gen=pow(g,m,p); mu=[pow(gen,t,p) for t in range(n)]
    bx=(np.outer(np.arange(p),np.array(mu)))%p
    return (w**bx).sum(axis=1)

def gauss_sums_order_dividing_m(p,n,g,m,dlog,w):
    """
    Characters trivial on mu_n  <=> characters of F_p^*/mu_n  (order m).
    A character chi_j defined by chi_j(g^a) = e^{2πi j a / (p-1)} for j multiple of n?
    The characters TRIVIAL on mu_n = <g^m> are chi with chi(g^m)=1 => chi(g)^m=1
    => chi = (base char)^{ (p-1)/m * t } = (base char)^{n t}, t=0..m-1.
    base char psi_1(g^a)=e^{2πi a/(p-1)}. So chi_t(g^a)=e^{2πi (n t) a/(p-1)}.
    Gauss sum g(chi_t) = Σ_{x≠0} chi_t(x) e_p(x).
    """
    # chi_t(x) for x=g^a is exp(2πi n t a/(p-1))
    a_of_x = dlog  # a_of_x[x]=a where x=g^a (for x in 1..p-1)
    G=np.zeros(m,dtype=complex)
    xs=np.arange(1,p)
    ax=a_of_x[xs]  # exponents
    ex=w**(xs%p)   # e_p(x)
    for t in range(m):
        chi = np.exp(2j*np.pi*(n*t%(p-1))*ax/(p-1))
        G[t]=(chi*ex).sum()
    return G

for n in [8,16]:
    for p in find_primes(n,4,1):
        g,m,dlog,w=setup(p,n)
        S=periods(p,n,w)
        G=gauss_sums_order_dividing_m(p,n,g,m,dlog,w)
        # Verify: |g(chi_t)|=sqrt(p) for t!=0, =? for t=0 (=-1? since Σ_{x≠0}e_p(x)=-1)
        absG=np.abs(G)
        print(f"n={n} p={p} m={m}: |g(chi_0)|={absG[0]:.3f} (expect 1, =|-1|), |g(chi_t)| t!=0 min/max={absG[1:].min():.4f}/{absG[1:].max():.4f}  sqrt(p)={math.sqrt(p):.4f}")
        # The period <-> Gauss sum DFT relation:
        # eta_b = Σ_{x∈μ_n} e_p(bx).  Claim: eta_b = (1/m) Σ_t chī_t(b) g(chi_t) ... let's test for several b
        # Standard: Σ_{x∈μ_n} e_p(bx) = (1/m)Σ_{t} \bar{chi_t}(b) g(chi_t)? check b=1 (in μ_n? b general nonzero)
        # Actually indicator of μ_n via characters trivial on μ_n: 1_{μ_n}(y)=(1/m)Σ_t chi_t(y) for y≠0.
        # Then eta_b=Σ_{y≠0}1_{μ_n}(y)e_p(by)=(1/m)Σ_t Σ_y chi_t(y)e_p(by)
        #       =(1/m)Σ_t \bar{chi_t}(b) g(chi_t)  (since Σ_y chi_t(y)e_p(by)=\bar chi_t(b) g(chi_t))
        recon=np.zeros(p,dtype=complex)
        ax=dlog
        for t in range(m):
            chib = np.exp(-2j*np.pi*(n*t%(p-1))*ax/(p-1))  # \bar chi_t(b), b=1..p-1
            recon[1:]+= chib[1:]*G[t]
        recon/=m
        err=np.abs(recon[1:]-S[1:]).max()
        print(f"   DFT reconstruction error eta_b vs (1/m)Σ chī_t(b)g(chi_t): {err:.2e}")
