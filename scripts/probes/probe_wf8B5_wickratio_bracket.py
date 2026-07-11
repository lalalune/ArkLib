# Reconcile: R antitone  <=> which concavity?
# R(r)=m_{r+1}/m_r. R(r+1)<=R(r) means m_{r+2}/m_{r+1} <= m_{r+1}/m_r
#  => m_{r+2} m_r <= m_{r+1}^2  => m_{r+1}^2 >= m_r m_{r+2}  => LOG-CONCAVE.
# So W3-anti (R antitone) = m_r LOG-CONCAVE. The brief's "log-convex" is a mislabel.
# This is GOOD news: log-concavity of a Wick-normalized moment sequence is the NATURAL
# direction and follows from a Hankel-type / Turan structure on the NORMALIZED moments.
#
# Now: m_r = M(r)/W_r. m_r log-CONCAVE <=> M(r+1)/W_{r+1} * M(r-1)/W_{r-1} <= (M(r)/W_r)^2
#   <=> M(r+1)M(r-1)/M(r)^2 <= W_{r+1}W_{r-1}/W_r^2 = (2r+1)/(2r-1)  [the Wick log-convex ratio]
# So m_r log-concave <=> the RAW moment log-convexity DEFECT ratio
#   Q(r):=M(r+1)M(r-1)/M(r)^2  satisfies  Q(r) <= (2r+1)/(2r-1).
# We KNOW Q(r)>=1 (Hankel/Cauchy-Schwarz, PROVEN energy_logConvex). The question is the UPPER
# bound Q(r) <= 1 + 2/(2r-1). Let's measure Q(r) and the gap.
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
for (n,lo) in [(16,60000),(32,1000000),(64,16000000),(128,260000000)]:
    p=fp(n,lo);eta,m=etas(n,p)
    def M(r):return sum(e**(2*r) for e in eta)/m
    Ms=[M(r) for r in range(0,12)]
    print(f"n={n:4} lnq={log(p):.1f}")
    for r in range(1,9):
        Q=Ms[r+1]*Ms[r-1]/Ms[r]**2
        wick=(2*r+1)/(2*r-1)
        print(f"  r={r}: Q(r)=M(r+1)M(r-1)/M(r)^2={Q:.5f}  Wick(2r+1)/(2r-1)={wick:.5f}  Q<=Wick: {Q<=wick+1e-12}  slack={wick-Q:+.5f}")
