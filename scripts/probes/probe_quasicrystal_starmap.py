import numpy as np
# Cut-and-project / internal-space test for mu_n (n=2^k) in F_p.
# Lens: the period eta_b = sum_{x in mu_n} e_p(bx) is the Fourier coeff (structure factor) of the
# weighted point set. In model-set theory the structure factor at b factors as (lattice sum)*(window
# transform in INTERNAL space). For mu_n the "internal space" = the other Galois embeddings of Z[zeta_n]
# / the dual subgroup characters chi_j (j in Z/m). eta_b = (-1 + sum_j tau(chi_j) e(-jc/m))/... .
# TEST: is M controlled by a SINGLE large |tau| (Bragg) or the SUM (continuous bg)? And does the
# worst c* land where the Gauss-sum PHASES align (a near-coherent-sum / large-deviation event)?

def isprime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
def primroot(p):
    phi=p-1; f=[]; t=phi; d=2
    while d*d<=t:
        if t%d==0:
            f.append(d)
            while t%d==0: t//=d
        d+=1
    if t>1: f.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in f): return g
    return None
def find_prime(n, beta):
    target=int(n**beta); m0=max(2,target//n)
    for m in range(m0,m0+200000):
        p=m*n+1
        if isprime(p) and p>n**3 and m>1: return p,m
    return None,None

for n in [8,16,32]:
    p,m=find_prime(n,4)
    g=primroot(p)
    mu=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    w=np.exp(2j*np.pi/p)
    etas=np.array([sum(w**((pow(g,c,p)*x)%p) for x in mu) for c in range(m)])
    mags=np.abs(etas)
    cstar=int(np.argmax(mags)); M=mags[cstar]
    # The period vector (eta_c) is the inverse-DFT of the Gauss-sum sequence (tau(chi_j)).
    # Recover tau via forward DFT of etas (up to the -1/m principal term):
    tau = np.fft.fft(etas)   # tau[j] ~ m*coeff; |tau[j]| should be ~ sqrt(p) for j!=0
    taumag=np.abs(tau)/np.sqrt(p)   # normalized; expect ~1 for j!=0 (Gauss sum modulus)
    # Bragg vs background: if M came from ONE coherent tau term, M ~ sqrt(p)/m*... ; if from coherent
    # SUM of all m phases at c*, M ~ sqrt(p)*sqrt(m)/m = sqrt(p/m)=sqrt(n). Measure the "phase coherence"
    # at c*: how concentrated is the contribution of each j to eta_{c*}?
    phases = np.array([tau[j]*np.exp(-2j*np.pi*j*cstar/m) for j in range(1,m)])
    coherent_real = phases.real.sum()
    L1 = np.abs(phases).sum()
    coherence = abs(phases.sum())/L1   # 1 = fully aligned (huge dev), ~1/sqrt(m) = random
    print(f"n={n} p={p} m={m}: M={M:.2f} sqrt(n)={np.sqrt(n):.2f} | "
          f"mean|tau|/sqrt(p)={taumag[1:].mean():.3f} (flat Gauss-sum check) | "
          f"phase-coherence at c*={coherence:.4f} (rand~{1/np.sqrt(m):.4f}) | "
          f"coherence/random={coherence*np.sqrt(m):.2f}")
