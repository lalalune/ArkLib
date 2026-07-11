# Pin the q-threshold for USG / m_1<=1 at fixed n=64. m_1 = M_2/(n*W_1)= E[X^4]/(3 n E[X^2]/n)... 
# Actually m_1 = M(1)/W_1 = E[X^2]/n. Wait recompute: M(r)=(1/m)sum eta^{2r}, W_r=(2r-1)!!n^r.
# m_1 = M(1)/(1*n) = E[X^2]/n. By Parseval E[X^2] = (1/m) sum_{b!=0} eta_b^2.
# sum_{all b} eta_b^2 = q * n (Parseval-ish), minus principal (b=0 gives eta_0=n, contributes n^2).
# So (1/m) sum_{b!=0} eta_b^2 = (qn - n^2)/(q-1) = n(q-n)/(q-1) -> n as q->inf, but >n? 
# n(q-n)/(q-1): for q>n, (q-n)/(q-1)<1 so m_1 = (q-n)/(q-1) <1 ALWAYS?? but probe showed 1.2355.
# Recheck: maybe my M index. The brief: m_0=1, m_r=M(r)/W_r, R(1)=m_2/m_1. m_1=M(1)/W_1.
# Let me just directly compute m_1 and m_2 and the kurtosis cap M_4<=3 n M_2 (W3-base) vs q.
import math
from math import pi, cos, log
def isp(n):
    if n<2:return False
    d=2
    while d*d<=n:
        if n%d==0:return False
        d+=1
    return True
def fp(n,lo):
    p=lo+((1+n-lo%n)%n)
    if p<=2:p+=n
    while True:
        if p>2 and p%n==1 and isp(p):return p
        p+=n
def proot(p):
    m=p-1;fs=[];d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fs.append(m)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs):return g
        g+=1
def etas(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p)
    mu=[pow(h,j,p) for j in range(n)]
    m=(p-1)//n;gn=pow(g,n,p)
    eta=[];b=1
    for _ in range(m):
        re=sum(cos(2*pi*((b*x)%p)/p) for x in mu)
        eta.append(re);b=(b*gn)%p
    return eta,m
n=64
print(f"n={n}: kurtosis cap M4<=3n*M2 (W3-base) and USG across growing q:")
for lo in [600,2000,8000,30000,120000,500000,2000000,8000000]:
    p=fp(n,lo);eta,m=etas(n,p)
    M2=sum(e**4 for e in eta)/m     # = M(2) in brief notation (E[X^4])
    M1=sum(e**2 for e in eta)/m     # E[X^2]
    M3=sum(e**6 for e in eta)/m
    # W3-base kurtosis: M(2)/W_2 <= M(1)/W_1 i.e. m_2<=m_1: E[X^4]/(3n^2) <= E[X^2]/n
    #   <=> E[X^4] <= 3 n E[X^2].  beta=log(p)/log(n).
    cap = 3*n*M1
    ok = M2<=cap*(1+1e-9)
    beta=log(p)/log(n)
    print(f"  p={p:>10} beta={beta:.2f} | E[X^2]={M1:.2f} E[X^4]={M2:.1f} 3nE[X^2]={cap:.1f} | M4<=3nM2: {ok} ratio={M2/cap:.4f}")
