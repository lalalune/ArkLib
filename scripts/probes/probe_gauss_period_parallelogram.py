import numpy as np, math
from sympy import isprime
def find_prime(target, mod):
    p = target + ((1 - (target % mod)) % mod)
    while not isprime(p): p += mod
    return p
def order_elt(p, n):
    def pf(m):
        f=set(); d=2
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    for g in range(2,p):
        z=pow(g,(p-1)//n,p)
        if all(pow(z,n//q,p)!=1 for q in pf(n)): return z
    raise RuntimeError
def analyze(p,n):
    z=order_elt(p,n)
    mu=[pow(z,j,p) for j in range(n)]
    ind=np.zeros(p)
    for x in mu: ind[x]=1.0
    F=np.fft.fft(ind); absF=np.abs(F[1:])
    Muntw=float(absF.max()); bstar=int(np.argmax(absF))+1
    indchi=np.zeros(p)
    for j in range(n): indchi[mu[j]] = 1.0 if j%2==0 else -1.0
    Fchi=np.fft.fft(indchi); Mtw=float(np.abs(Fchi[1:]).max())
    b=bstar; w=np.exp(-2j*np.pi/p)
    half=[pow(z,2*j,p) for j in range(n//2)]
    A=sum(w**((b*x)%p) for x in half); B=sum(w**((b*z*x)%p) for x in half)
    cosang=float((np.conj(A)*B).real/(abs(A)*abs(B))) if abs(A)*abs(B)>1e-9 else 0.0
    return Muntw,Mtw,abs(A),abs(B),cosang,abs(A-B)
print(f"{'mu':>3}{'n':>5}{'p':>9}{'M_untw':>9}{'M_tw':>8}{'M/√(nln(p/n))':>15}{'cos(A,B)@b*':>12}{'growth':>8}",flush=True)
prev=None
for mu in [3,4,5]:
    n=2**mu; p=find_prime(n**4,n)
    Mu,Mt,a,b,c,amb=analyze(p,n)
    norm=math.sqrt(n*math.log(p/n)); g=(Mu/prev) if prev else 0.0
    print(f"{mu:>3}{n:>5}{p:>9}{Mu:>9.2f}{Mt:>8.2f}{Mu/norm:>15.3f}{c:>12.4f}{g:>8.3f}",flush=True)
    prev=Mu
