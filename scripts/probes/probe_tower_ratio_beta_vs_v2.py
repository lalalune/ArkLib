import cmath, math
from math import log, sqrt
import statistics
def isprime(m):
    if m<2:return False
    if m%2==0:return m==2
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
def v2(x):
    c=0
    while x%2==0:x//=2;c+=1
    return c
def Mof(p,n):
    g=primroot(p);h=pow(g,(p-1)//n,p)
    mun=[pow(h,j,p) for j in range(n)]
    w=2*math.pi/p
    return max(abs(sum(cmath.exp(1j*w*((b*y)%p)) for y in mun)) for b in range(1,p))
n=16
# CURATED: pairs at similar beta but different v2, and similar v2 different beta
# (p, label)
sel=[
 # beta ~ 2.4-2.6, vary v2:
 769,   # v2=8 beta2.40
 881,   # 880=16*55 v2=4 beta2.45 -- check
 1009,  # 1008=16*63 v2=4
 1153,  # v2=7 beta2.53
 # beta ~ 3.4, vary v2
 12289, # v2=12 beta3.40
 11489, # 11488=16*718=16*2*359 v2=5
]
# build programmatically instead: collect primes, bucket by beta band, print
prs=[]
p=97
cnt=0
while p<30000 and cnt<80:
    if isprime(p) and (p-1)%n==0 and (p-1)//n>=2:
        prs.append(p); cnt+=1
    p+=16
import random
random.seed(1)
random.shuffle(prs)
prs=prs[:34]
rows=[]
for p in prs:
    a=v2(p-1); beta=log(p)/log(n)
    Mn=Mof(p,n); Mh=Mof(p,n//2)
    m_n=(p-1)//n
    Rn=Mn/sqrt(n*log(m_n))
    rows.append((p,a,beta,Rn,Mn/Mh))
print(f"{'p':>7} {'v2':>3} {'beta':>5} {'R(n)':>6} {'ratio':>6}")
for r in sorted(rows,key=lambda x:(x[1],x[2])):
    print(f"{r[0]:>7} {r[1]:>3} {r[2]:>5.2f} {r[3]:>6.3f} {r[4]:>6.3f}")
vs=[r[1] for r in rows];bs=[r[2] for r in rows];Rns=[r[3] for r in rows];rats=[r[4] for r in rows]
def corr(a,b):
    ma,mb=statistics.mean(a),statistics.mean(b)
    return sum((x-ma)*(y-mb) for x,y in zip(a,b))/(sqrt(sum((x-ma)**2 for x in a))*sqrt(sum((y-mb)**2 for y in b)))
print(f"\nN={len(rows)}")
print(f"corr(v2,R)={corr(vs,Rns):.3f} corr(beta,R)={corr(bs,Rns):.3f} corr(v2,beta)={corr(vs,bs):.3f}")
print(f"corr(v2,ratio)={corr(vs,rats):.3f} corr(beta,ratio)={corr(bs,rats):.3f}")
