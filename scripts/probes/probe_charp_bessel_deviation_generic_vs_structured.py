import numpy as np, math
from scipy.special import i0
from sympy import primitive_root
def isp(x):
    if x<2:return False
    if x%2==0:return x==2
    d=3
    while d*d<=x:
        if x%d==0:return False
        d+=2
    return True
def is_fermat_like(p):
    # flag structured: p-1 a pure power of 2 (Fermat), or p = 2^k+1
    q=p-1
    return (q & (q-1))==0
def gen_primes(n, beta_lo=3.1, count=3, skip_structured=True):
    out=[]; t=((int(n**beta_lo))//n)*n+1
    while len(out)<count:
        if t>n+1 and isp(t) and (not skip_structured or not is_fermat_like(t)): out.append(t)
        t+=n
    return out
def logmeanexp(x): M=x.max(); return M+math.log(np.mean(np.exp(x-M)))
def Dprobe(n,p):
    g=primitive_root(p); m=(p-1)//n; h=pow(g,(p-1)//n,p)
    mun=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64); w=2*math.pi/p
    reps=np.array([pow(g,j,p) for j in range(m)],dtype=np.int64)
    eta=np.empty(m)
    for i in range(0,m,8192):
        b=reps[i:i+8192][:,None]; eta[i:i+8192]=np.cos(w*((b*mun[None,:])%p)).sum(1)
    saddle=math.sqrt(2*math.log(m)/n); t=saddle
    D=logmeanexp(t*eta)-(n/2)*math.log(i0(2*t))
    return m, eta.max(), eta.max()/math.sqrt(2*n*math.log(m)), D
print("n | p | structured? | m | max/sqrt(2n logm) | D(t*)  (D<=0 => sub-baseline, floor holds)")
for n in [16,32,64]:
    for p in gen_primes(n, count=3, skip_structured=True):
        m,Mx,ratio,D=Dprobe(n,p)
        print(f"{n} | {p} | gen | {m} | {ratio:.3f} | {D:+.4f} {'SUB' if D<=1e-9 else 'ABOVE'}")
    # explicitly include the Fermat F4 for n=32 contrast
    if n==32:
        m,Mx,ratio,D=Dprobe(32,65537); print(f"32 | 65537=F4 | STRUCTURED | {m} | {ratio:.3f} | {D:+.4f} {'SUB' if D<=1e-9 else 'ABOVE'}  <- Fermat")
