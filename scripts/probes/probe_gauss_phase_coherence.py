import cmath, math
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,target):
    p=target-(target%n)+1
    for d in range(0,40*n,n):
        if is_prime(p+d):return p+d
    return None
def primitive_root(p):
    # find generator of F_p*
    facs=set(); m=p-1; d=2
    while d*d<=m:
        while m%d==0:facs.add(d);m//=d
        d+=1
    if m>1:facs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs):return g
    return None
def analyze(n,p):
    g=primitive_root(p); f=(p-1)//n; tp=2*math.pi
    # index (discrete log) table
    ind={}; cur=1
    for i in range(p-1): ind[cur]=i; cur=cur*g%p
    # characters trivial on mu_n: chi_j(x)=e(2πi j ind(x)/(p-1)) with j multiple of n? 
    # chi trivial on mu_n=<g^f>: chi(g^f)=1 => chi(g)=e(2πi t/(p-1)) with t*f ≡0 mod(p-1) => t multiple of n. t=n*s, s=0..f-1.
    # Gauss sum g(chi_s)=Σ_{x≠0} chi_s(x) e_p(x)
    def chi(s,x):  # chi_s(x), x in F_p*
        return cmath.exp(1j*tp*(n*s*ind[x])/(p-1))
    # eta_b directly
    H=[pow(g,(p-1)//n*i,p) for i in range(n)]  # mu_n = <g^f>
    def eta(b):
        return sum(cmath.exp(1j*tp*((b*x)%p)/p) for x in H)
    # compute Gauss sums g(chi_s) for s=0..f-1
    Gs=[]
    for s in range(f):
        gs=sum(chi(s,x)*cmath.exp(1j*tp*x/p) for x in range(1,p))
        Gs.append(gs)
    # verify eta_b = (1/f) Σ_s conj(chi_s(b)) g(chi_s)  [for b≠0]
    # and measure coherence: |eta_{b*}| vs sqrt(p), and the phase alignment
    etas=[abs(eta(b)) for b in range(1,p)]
    M=max(etas); bstar=etas.index(M)+1
    # reconstruct via gauss
    recon=abs(sum((chi(s,bstar).conjugate())*Gs[s] for s in range(f))/f)
    # coherence factor: M / (mean|g|/sqrt(f)) ... |g|=sqrt(p) each, f terms
    sqp=math.sqrt(p)
    # incoherent prediction: |eta|~ sqrt(f)*sqrt(p)/f = sqrt(p/f)=sqrt(n)
    print(f"n={n} p={p} f={f}: M={M:.2f}, √p={sqp:.1f}, √(2n ln p)={math.sqrt(2*n*math.log(p)):.2f}, M/√n={M/math.sqrt(n):.2f}")
    print(f"   |g(χ_s)| (should all=√p={sqp:.1f}): min={min(abs(x) for x in Gs[1:]):.2f} max={max(abs(x) for x in Gs[1:]):.2f}")
    print(f"   recon eta_b* via Gauss = {recon:.2f} (=M? {abs(recon-M)<1e-6})")
    # coherence at b*: the terms conj(chi_s(b*))*g(chi_s) — their phases. If aligned, |sum|=f*√p; measure
    terms=[(chi(s,bstar).conjugate())*Gs[s] for s in range(1,f)]  # exclude s=0 (principal)
    coh = abs(sum(terms))/(sum(abs(t) for t in terms))  # 1=coherent, ~1/sqrt(f)=incoherent
    print(f"   coherence at b* (excl principal): {coh:.3f}  (1=resonance/√p, ~1/√f={1/math.sqrt(f):.3f}=incoherent/√n)")
for (n,beta) in [(8,3),(8,4),(16,3)]:
    p=find_prime(n,int(round(n**beta)))
    if p and p<60000: analyze(n,p)
