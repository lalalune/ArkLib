# Is SubGaussianTailBound TRUE-but-open or FALSE-as-stated?
# Test: empirical moment ratio R_r = (mean_b |eta_b|^{2r}) / ((2r-1)!! n^r)  [=1 iff Gaussian/sub-Gaussian with proxy n]
# at r = crossover (~beta+1) and r = needed depth (~log_2 m). If R_r stays ~1 (or bounded) -> sub-Gaussian plausible (open);
# if R_r grows fast at depth -> the literal sub-Gaussian tail is FALSE (forced anomaly), only the MAX bound survives.
import numpy as np, math
from sympy import primitive_root
def isprime(x):
    if x<2:return False
    if x%2==0:return x==2
    d=3
    while d*d<=x:
        if x%d==0:return False
        d+=2
    return True
def find_p(n,beta=4.0):
    t=((int(n**beta))//n)*n+1
    while not(t>n+1 and isprime(t)): t+=n
    return t
def dblfact(k):  # (2r-1)!!
    r=1.0
    for j in range(1,2*k,2): r*=j
    return r
def periods(p,n):
    g=primitive_root(p); m=(p-1)//n; h=pow(g,m,p)
    mun=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    w=2*math.pi/p
    reps=np.array([pow(g,j,p) for j in range(m)],dtype=np.int64)
    out=np.empty(m)
    CH=8192
    for i in range(0,m,CH):
        b=reps[i:i+CH][:,None]
        out[i:i+CH]=np.abs(np.exp(1j*w*((b*mun[None,:])%p)).sum(1))
    return out,m
print("n | p | m | beta+1 | needed_depth log2(m) | R_{beta+1} | R_{depth} | max|eta|/sqrt(2n log m)")
for n in [16,32,64,128]:
    p=find_p(n,4.0); a,m=periods(p,n)
    a2=a**2/n           # |eta|^2 / n  (normalized, mean ~1)
    depth=max(2,round(math.log2(m)))
    rcross=5            # ~beta+1 for beta=4
    def R(r):
        return float(np.mean(a2**r))/dblfact(r)   # mean(|eta|^{2r})/((2r-1)!! n^r)
    floor=math.sqrt(2*n*math.log(m))
    print(f"{n} | {p} | {m} | r={rcross} | r={depth} | {R(rcross):.3f} | {R(depth):.2e} | {a.max()/floor:.3f}")
