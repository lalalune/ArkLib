# Efficient non-saturated n=64 check via meet-in-the-middle:
# pick antipodal-free 4 elts; need 2 more u5,u6 in mu_64 with u5+u6=-S4, u5^3+u6^3=-T4.
# Then P=u5 u6=(s^3 - t)/(3s); u5,u6 = roots of z^2 - s z + P; check in mu_64, antipodal-free, distinct.
from itertools import combinations
from sympy import primerange, sqrt_mod
n=64; HALF=32
def check_prime(p, max4=10000000):
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    i2=pow(2,p-2,p); i3=pow(3,p-2,p)
    mu=[pow(g,j,p) for j in range(n)]
    muset={mu[j]:j for j in range(n)}
    mu32=[pow(g,2*l,p) for l in range(HALF)]
    Sig=set(sum(W)%p for W in combinations(mu32,3))
    sat=len(Sig)/p
    prim=0; cex=0; cnt4=0
    for c4 in combinations(range(n),4):
        if any(((j+HALF)%n) in set(c4) for j in c4): continue
        cnt4+=1
        if cnt4>max4: break
        us4=[mu[j] for j in c4]
        S4=sum(us4)%p; T4=sum(pow(u,3,p) for u in us4)%p
        s=(-S4)%p
        if s==0: continue
        P=((pow(s,3,p)-(-T4))%p)*i3%p*pow(s,p-2,p)%p
        # roots of z^2 - s z + P: disc = s^2-4P
        disc=(s*s-4*P)%p
        r=sqrt_mod(disc,p)
        if r is None: continue
        u5=((s+r)*i2)%p; u6=((s-r)*i2)%p
        if u5 not in muset or u6 not in muset: continue
        j5,j6=muset[u5],muset[u6]
        U=set(c4)|{j5,j6}
        if len(U)!=6: continue
        if any(((j+HALF)%n) in U for j in U): continue   # antipodal-free full check
        # verify
        us=[mu[j] for j in U]
        if sum(us)%p!=0 or sum(pow(u,3,p) for u in us)%p!=0: continue
        prim+=1
        e2=(-i2*sum(pow(u,2,p) for u in us))%p
        if e2 not in Sig: cex+=1
    return (p, round(sat,3), len(Sig), prim, cex)

print("char-0 |Sigma_3|(mu_32)=4512; non-saturated needs p>>4512")
for p in [10177,12289,12553,13441,15233,17089,21121,40961]:
    res=check_prime(p)
    if res:
        print(f"  p={res[0]} sat={res[1]} |Sigma_3|={res[2]} primitive_found={res[3]} e2-OUT-of-Sigma={res[4]}"
              + ("  <<< NON-SATURATED COUNTEREXAMPLE" if res[4]>0 and res[1]<0.6 else ""))
    # stop after a handful of non-saturated primes
