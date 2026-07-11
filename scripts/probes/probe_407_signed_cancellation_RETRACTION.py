import math, cmath
def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def fs(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def pr(p):
    fac=list(fs(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def fp(t,mod):
    k=max(1,round(t/mod))
    for d in range(0,400000):
        for s in (1,-1):
            kk=k+s*d
            if kk<1: continue
            p=kk*mod+1
            if p>3 and is_prime(p): return p
def sub(n,p):
    g=pr(p); h=pow(g,(p-1)//n,p); e=[];x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e
def per(e,p):
    w=2*math.pi/p
    return [sum(cmath.exp(1j*w*((b*x)%p)) for x in e).real for b in range(p)]
# What survives: my EVEN-r C_r table. C_r(even) = (sum|eta_b|^r)/((p-1)M^r) = AVERAGE of (|eta_b|/M)^r.
# This is the moment-DISTRIBUTION concentration: how much mass is near the max M. Thin smaller =>
# fewer b near M (M is a sharper outlier in thin). Is THAT thinness-essential & exploitable?
# It's the ratio (mean |eta|^r)/(max|eta|^r). For the M-bound M<=(sum|eta|^{2r})^{1/2r}, the slack is
# exactly ((p-1) * mean|eta|^{2r})^{1/2r}/M = ((p-1) C_{2r... })... = (p-1)^{1/2r} * C_{2r}^{1/2r}? 
# Reconcile with the THICKNESS-INVARIANT cert/true~1.18: cert/true = (sum|eta|^{2r})^{1/2r}/M
#   = ((p-1) * C_{2r}^{abs} * M^{2r})^{1/2r}/M ... where my C_r used M^r not M^{2r}. Let me just
# directly recompute cert/true per regime to confirm it's STILL thickness-invariant (the real result).
print("CONFIRM the surviving real result: cert/true = min_r (sum_{b!=0}|eta_b|^{2r})^{1/2r} / M")
for n in [8,16]:
    for beta in [2.5,3.0,4.0]:
        if n==16 and beta>4.0: continue
        p=fp(int(n**beta),n)
        e=sub(n,p); eta=per(e,p)
        M=max(abs(eta[b]) for b in range(1,p))
        best=1e18;br=0
        for r in range(1,14):
            s=sum(abs(eta[b])**(2*r) for b in range(1,p))
            c=s**(1.0/(2*r))
            if c<best: best=c;br=r
        print(f"  n={n} beta={math.log(p)/math.log(n):.2f}: cert/true={best/M:.4f} (r*={br})")
