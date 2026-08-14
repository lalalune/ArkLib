import numpy as np
from math import log, sqrt, lgamma, exp

def gauss_abs(p,n):
    pm1=p-1
    def factor(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    fs=factor(pm1);g=2
    while not all(pow(g,pm1//q,p)!=1 for q in fs):g+=1
    h=pow(g,pm1//n,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.float64)
    b=np.arange(1,p,dtype=np.float64)
    ang=2*np.pi*np.outer(b,mu)/p
    return np.abs(np.cos(ang).sum(1)+1j*np.sin(ang).sum(1))

# Sufficient lemma (moment method): M(n)^{2k} <= sum_{b!=0} |S_b|^{2k} = p * Ehat_k
# where Ehat_k = (1/p)*[char-p energy E_k]  and E_k = #{r-fold +-1 coincidences mod p}.
# To get M <= C sqrt(n log(p/n)) we need at k* ~ log(p/n):  p * E_k <= (C^2 n log(p/n))^k.
# i.e. E_k <= n^k * (C^2 log(p/n))^k / p ... but p^{1/2k}=exp(log p/2k). With k=log(p/n)/2:
# Target SUFFICIENT INEQUALITY:  E_k(mu_n) <= (2k-1)!! * n^k  for all k <= ~log p   (Gaussian/Wick moments)
#  -> then M^{2k} <= p*(2k-1)!!*n^k, M <= (p (2k-1)!! n^k)^{1/2k}.  Optimize k.
# (2k-1)!! ~ (2k/e)^k sqrt(2). So M^{2k} <= p*(2k/e)^k*n^k => M <= p^{1/2k} sqrt(2kn/e).
# choose k=log p /2: p^{1/2k}=e^{1}=e... hmm. choose k=(1/2)log(p): p^{1/2k}=sqrt(e).
# Then M <= sqrt(e)*sqrt(log(p)*n/e)=sqrt(n log p). Close to prize (log p vs log(p/n)).
# refine: M^{2k}<= p (2k-1)!! n^k. log: 2k log M <= log p + log((2k-1)!!)+k log n
#   log((2k-1)!!)= lgamma(2k+1)-k*log(2)-lgamma(k+1)  (since (2k-1)!!=(2k)!/(2^k k!))
print("If Wick lemma E_k <= (2k-1)!! n^k held to depth log p, predicted M-bound vs actual M & prize:")
print(f"{'n':>4} {'p':>7} {'M':>8} {'prize':>8} {'WickBnd':>9} {'k*':>4} {'actualE_k/Wick@k*':>16}")
for n,p in [(8,10169),(16,65537),(32,65921),(64,65921),(128,65921)]:
    if (p-1)%n:continue
    a=gauss_abs(p,n);a2=a**2;M=a.max();prize=sqrt(n*log(p/n))
    best=1e18;bk=0;ratio=0
    for k in range(1,int(log(p))+2):
        wick=exp(lgamma(2*k+1)-k*log(2)-lgamma(k+1))*n**k  # (2k-1)!! n^k
        bnd=(p*wick)**(1.0/(2*k))
        if bnd<best:
            best=bnd;bk=k
            Ek_actual=(a2.astype(float)**k).sum()  # = sum_{b!=0}|S_b|^{2k} = p*Ehat... actually char energy*? 
            # sum_{b!=0}|S_b|^{2k} ; Ehat_k:=that. Wick predicts <= p*wick? compare Ehat to p*wick? 
            # Actually E_k(integer count)= sum_{all b}|S_b|^{2k}/p. sum_{b!=0}=p*E_k - n^{2k}.
            Ek=(a2.astype(float)**k).sum()/p + n**(2*k)/p  # add b=0 term n^{2k}, /p
            ratio=Ek/wick
    print(f"{n:>4} {p:>7} {M:8.3f} {prize:8.3f} {best:9.3f} {bk:>4} {ratio:16.3f}")

print()
print("CHECK the actual E_k <= (2k-1)!! n^k inequality directly (char-p energy Wick bound), all k:")
for n,p in [(16,65537),(64,65921),(128,65921)]:
    if (p-1)%n:continue
    a=gauss_abs(p,n);a2=a**2.0
    viol=[]
    for k in range(1,20):
        wick=exp(lgamma(2*k+1)-k*log(2)-lgamma(k+1))*n**k
        Ek=(a2**k).sum()/p + n**(2*k)/p
        if Ek>wick: viol.append((k, Ek/wick))
    print(f"n={n} p={p}: Wick violations (k, E_k/Wick): {viol[:8]}")
