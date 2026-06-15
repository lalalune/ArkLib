"""
SHARPEN: M(n)/M(n/2) GROWS with v2(p-1) at fixed n. Is this the structured-prime mechanism?
Also test the COSET DECOMPOSITION: eta_b(mu_n) = eta_b(mu_{n/2}) + eta_b(g*mu_{n/2}) where
mu_n = mu_{n/2} cup g*mu_{n/2} (g a primitive n-th root). At the spike argmax b*, are the two
coset-periods CONSTRUCTIVELY aligned (tower amplification) or random-phase (independent)?
"""
import cmath, math
from math import gcd, log, sqrt

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0:continue
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
    return None
def v2(x):
    c=0
    while x%2==0:x//=2;c+=1
    return c

def analyze(p,n):
    g=primroot(p); h=pow(g,(p-1)//n,p)   # primitive n-th root
    mun=[pow(h,j,p) for j in range(n)]
    # mu_{n/2} = even powers of h = <h^2>
    muh=[pow(h,2*j,p) for j in range(n//2)]
    w=2*math.pi/p
    def period_arr(elems):
        return [abs(sum(cmath.exp(1j*w*((b*y)%p)) for y in elems)) for b in range(p)]
    arrn=period_arr(mun); 
    Mn=max(arrn[1:]); bstar=arrn.index(Mn)
    # coset decomposition at b*: mu_n = muh cup (h*muh)
    cosetA=muh; cosetB=[(h*y)%p for y in muh]
    etaA=sum(cmath.exp(1j*w*((bstar*y)%p)) for y in cosetA)
    etaB=sum(cmath.exp(1j*w*((bstar*y)%p)) for y in cosetB)
    # alignment: |etaA+etaB| vs |etaA|+|etaB| (constructive) vs sqrt(|etaA|^2+|etaB|^2) (random)
    total=abs(etaA+etaB)
    constructive=abs(etaA)+abs(etaB)
    random_model=sqrt(abs(etaA)**2+abs(etaB)**2)
    phase_align=math.cos(cmath.phase(etaA)-cmath.phase(etaB))  # 1=aligned,0=orthog,-1=opposed
    arrh=period_arr(muh); Mh=max(arrh[1:])
    return Mn,Mh,bstar,abs(etaA),abs(etaB),total,constructive,random_model,phase_align

print(f"{'p':>8} {'v2':>3} {'n':>4} {'M(n)':>7} {'M(n/2)':>7} {'rat':>5} {'|etaA|':>7} {'|etaB|':>7} {'|A+B|':>7} {'rand':>6} {'cosphi':>7} {'verdict'}")
for p in [97,193,257,449,577,769,1153,3329,7681,12289,40961,65537,114689,163841,786433]:
    if not isprime(p): continue
    a=v2(p-1)
    for n in [16,32]:
        if (p-1)%n: continue
        if p>100000 and n>16: continue
        Mn,Mh,bstar,eA,eB,tot,con,rnd,cphi=analyze(p,n)
        rat=Mn/Mh
        # verdict: is spike from constructive coset alignment?
        if cphi>0.5: v="CONSTRUCTIVE(tower-amp)"
        elif cphi<-0.3: v="opposed"
        else: v="~random"
        print(f"{p:>8} {a:>3} {n:>4} {Mn:>7.2f} {Mh:>7.2f} {rat:>5.2f} {eA:>7.2f} {eB:>7.2f} {tot:>7.2f} {rnd:>6.2f} {cphi:>7.3f} {v}")
