import numpy as np, math
from sympy import isprime
def find_prime(t,m):
    p=t+((1-(t%m))%m)
    while not isprime(p): p+=m
    return p
def order_elt(p,n):
    def pf(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    for g in range(2,p):
        z=pow(g,(p-1)//n,p)
        if all(pow(z,n//q,p)!=1 for q in pf(n)):return z
    raise RuntimeError
for mu in [3,4]:
    n=2**mu; p=find_prime(n**4,n); z=order_elt(p,n)
    mug=[pow(z,j,p) for j in range(n)]
    ind=np.zeros(p)
    for x in mug: ind[x]=1.0
    F=np.fft.fft(ind); absF=np.abs(F[1:]); bstar=int(np.argmax(absF))+1
    # note: F[b]=sum_x exp(-2πi b x/p)=η_{-b}; the maximizer index b corresponds to coefficient -b? use w accordingly
    w=np.exp(-2j*np.pi/p)
    half=[pow(z,2*j,p) for j in range(n//2)]
    b=bstar
    A=sum(w**((b*x)%p) for x in half); B=sum(w**((b*z*x)%p) for x in half)
    # relation of b* to the group: is b* in μ_n? is b*·z^k pattern? is η_{b*} real?
    eta=A+B
    inmu = b in set(mug)
    # check b* * (the other half generator) ... print key facts
    print(f"n={n} p={p}: b*={b} in_μ_n={inmu}  A={A:.4f}  B={B:.4f}  A-B={abs(A-B):.2e}  η_b*={eta:.4f}  arg(η)={np.angle(eta):.4f}")
    # is b* a power of z? (b* ∈ μ_n means b* = z^j)
    if inmu: print(f"    b* = z^{mug.index(b)} (a root of unity!)")
    # is b*·ζ ≡ conjugate-related? check η_{b*} vs η_{b* * z^{-1}}
