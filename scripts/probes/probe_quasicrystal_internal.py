import numpy as np
# Prize-faithful: p PRIME, p=1 mod n, mu_n PROPER 2-power subgroup, p >> n^3, NEVER n=p-1.
# Object: M(mu_n)=max_{b!=0}|sum_{x in mu_n} e_p(bx)| = max_c |eta_c|, eta_c Gaussian periods (deg m=(p-1)/n).
# Diffraction lens test: (A) conjugate-spread / Salem-vs-Pisot of the period vector;
#                        (B) the "internal space" structure -- do the m periods cluster (pure-point-like)
#                            or spread (continuous background)? The worst peak = sup of the spectrum.

def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def isprime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True

def find_prime(n, beta_target):
    # want p ~ n^beta, p prime, p = 1 mod n, p > n^3, index m=(p-1)/n > 1 (proper)
    target = int(n**beta_target)
    m0 = max(2, target//n)
    for m in range(m0, m0+200000):
        p = m*n+1
        if p % n != 1: continue
        if isprime(p) and p > n**3 and m>1:
            return p, m
    return None,None

def periods(n, p):
    # generator g of F_p^*
    def order_div(g):
        # check g is primitive root
        x=g%p; 
        # cheap: just trust trial; find primitive root
        return None
    # find primitive root
    def primroot(p):
        phi=p-1
        # factor phi
        f=[]; t=phi; d=2
        while d*d<=t:
            if t%d==0:
                f.append(d)
                while t%d==0: t//=d
            d+=1
        if t>1: f.append(t)
        for g in range(2,p):
            if all(pow(g,phi//q,p)!=1 for q in f): return g
        return None
    g=primroot(p)
    mu = sorted({pow(g, ((p-1)//n)*t, p) for t in range(n)})  # mu_n = n-th powers... actually subgroup of order n
    # mu_n = {g^(m*j): j} where m=(p-1)/n
    m=(p-1)//n
    mu=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    w=np.exp(2j*np.pi/p)
    # eta_c for c in 0..m-1: representative b=g^c
    etas=[]
    for c in range(m):
        b=pow(g,c,p)
        s=sum(w**((b*x)%p) for x in mu)
        etas.append(s)
    return np.array(etas), m

for n in [8,16,32]:
    for beta in [4]:
        p,m=find_prime(n,beta)
        if p is None: 
            print(f"n={n} beta={beta}: no prime"); continue
        etas,m=periods(n,p)
        mags=np.abs(etas)
        M=mags.max()
        rms=np.sqrt((mags**2).mean())  # ~ sqrt(n)
        floor=np.sqrt(2*n*np.log(p/n))
        # "Pisot test": is there ONE dominant period? ratio M / second-largest
        srt=np.sort(mags)[::-1]
        dom_ratio = srt[0]/srt[1] if len(srt)>1 else float('inf')
        # "Salem/balance": coefficient of variation of |eta|^2 (=1 means complex-Gaussian/random-like)
        cv = mags.std()/mags.mean()
        # internal-space clustering: fraction of periods within 0.5*M of the peak (Bragg-peak isolation)
        near = (mags > 0.7*M).mean()
        print(f"n={n} p={p} (~n^{np.log(p)/np.log(n):.2f}) m={m}: M={M:.2f} M/sqrt(n)={M/np.sqrt(n):.3f} "
              f"M/floor={M/floor:.3f} domRatio={dom_ratio:.3f} CV={cv:.3f} fracNearPeak={near:.4f}")
