# Quantify suppression of genuine relations: G_r vs random n^{2r}/p, across n/sqrt(p) regimes.
import cmath, math
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    for p in range(3,int(q**.5)+1,2):
        if q%p==0: return False
    return True
def primeat(n, beta):
    q=int(n**beta)
    while not(isprime(q) and (q-1)%n==0): q+=1
    return q
def genmu(p,n):
    e=(p-1)//n
    for a in range(2,p):
        z=pow(a,e,p)
        if pow(z,n//2,p)!=1: return z
def periods(n,p):
    z=genmu(p,n); 
    # primitive root via factor of p-1
    def fac(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    fs=fac(p-1); g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fs): g+=1
    m=(p-1)//n; zz=pow(g,m,p); G=[pow(zz,i,p) for i in range(n)]
    out=[];b=1
    for i in range(m):
        out.append(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G).real); b=b*g%p
    return out,m
def dbl(k):
    r=1
    for j in range(1,k+1,2): r*=j
    return r
print("E_r/E_r^0 (sub-Wick: <=1) and suppression G_r/(n^{2r}/p) across regimes",flush=True)
for n in [32,64]:
    for beta in [2.7, 4.0, 5.0]:
        p=primeat(n,beta); eta,m=periods(n,p)
        b_eff=math.log(p)/math.log(n); nsqp=n/math.sqrt(p)
        print(f" n={n} p={p} beta={b_eff:.2f} n/sqrt(p)={nsqp:.3f}:",flush=True)
        for r in [2,3,4,5]:
            Er=(n*sum(e**(2*r) for e in eta)+n**(2*r))/p
            Er0=dbl(2*r-1)*n**r
            Gr=Er-Er0; rand=n**(2*r)/p
            supp = Gr/rand if rand>0 else 0
            print(f"   r={r}: E_r/E_r^0={Er/Er0:.3f}  G_r/(n^2r/p)={supp:.4f}",flush=True)
