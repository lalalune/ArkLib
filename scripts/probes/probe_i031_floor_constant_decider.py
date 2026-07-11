# I031 DECIDER: does M(mu_n)/sqrt(n*log(p/n)) stabilize (handle real) or creep to inf (leaks to wall)?
# Exploit orbit-invariance: eta_b depends only on coset b*mu_n, so max over m=(p-1)/n coset reps.
import numpy as np, math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def find_p(n, betamin=3.05):
    # smallest prime p>n^betamin with n|p-1 (thin, p>n^3, NOT n=p-1)
    target=int(n**betamin)
    start=((target)//n)*n+1
    t=start
    while True:
        if t>n+1 and isprime(t): return t
        t+=n
def subgroup_gen_and_set(p,n):
    # generator g of F_p*, h=g^((p-1)/n) of order n; mu_n; and coset reps g^0..g^{m-1}
    # find primitive root
    from sympy import primitive_root
    g=primitive_root(p)
    m=(p-1)//n
    h=pow(g,m,p)
    mun=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    reps=np.array([pow(g,j,p) for j in range(m)],dtype=np.int64)  # coset reps (b != 0)
    return mun, reps, m
def M_of(p,n,cap_reps=200000):
    mun,reps,m=subgroup_gen_and_set(p,n)
    w=2*math.pi/p
    # sample reps if m too large (for the MAX, sampling gives a lower bound; flag if sampled)
    sampled = m>cap_reps
    if sampled:
        idx=np.linspace(0,m-1,cap_reps).astype(np.int64); reps=reps[idx]
    best=0.0
    CH=4096
    for i in range(0,len(reps),CH):
        b=reps[i:i+CH][:,None]                      # (B,1)
        prod=(b*mun[None,:])%p                       # (B,n)
        s=np.exp(1j*w*prod).sum(axis=1)              # (B,)
        mx=np.abs(s).max()
        if mx>best: best=mx
    return best,m,sampled
print("n | p | beta | m=(p-1)/n | M | sqrt(n*log(p/n)) | RATIO | M/sqrt(n) | sampled")
for n in [32,64,128]:
    p=find_p(n,4.0)
    M,m,samp=M_of(p,n)
    floor=math.sqrt(n*math.log(p/n))
    print(f"{n} | {p} | {math.log(p)/math.log(n):.2f} | {m} | {M:.2f} | {floor:.2f} | {M/floor:.4f} | {M/math.sqrt(n):.3f} | {samp}")
