import math, cmath, numpy as np
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def proot(p):
    m=p-1;fs=set();d=2
    while d*d<=m:
        if m%d==0:
            fs.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def find_p(n,beta):
    target=int(n**beta); lo=max(target,200003)
    m0=(lo+n-1)//n
    while True:
        p=n*m0+1
        if isprime(p) and (p-1)//n>1: return p
        m0+=1

# D7 height/Bogomolov prescreen:
# H1: count of "large cosets" #{b: |eta_b| > c sqrt(n)} stays small (subpoly) = height-gap signature
# H2: a moment bound using ONLY that count + the EXACT max-mass would give M; does it beat Johnson sqrt(n)?
print("D7 height/few-small-points prescreen: is M driven by a SUBPOLYNOMIAL set of resonant cosets?")
print(f"{'n':>5}{'beta':>5}{'p':>12}{'M/sqrtn':>9}{'#large':>8}{'m':>9}{'frac_large':>11}{'C':>7}")
for beta in [4.0]:
  for n in [16,32,64,128,256,512]:
    p=find_p(n,beta); g=proot(p); h=pow(g,(p-1)//n,p)
    mu=[pow(h,j,p) for j in range(n)]
    m=(p-1)//n
    # range b over a transversal: b=g^j, j=0..m-1 (each coset once)
    gn=pow(g,n,p); b=1; best=0.0
    mags=[]
    # cap work: if m huge, sample
    Bcap=min(m,40000)
    for _ in range(Bcap):
        t=[(b*x)%p for x in mu]
        re=sum(math.cos(2*math.pi*tt/p) for tt in t)
        im=sum(math.sin(2*math.pi*tt/p) for tt in t)
        mag=math.hypot(re,im); mags.append(mag)
        if mag>best:best=mag
        b=(b*gn)%p
    mags=np.array(mags)
    thr=1.5*math.sqrt(n)   # "large" = clearly above white-noise sqrt(n)
    nlarge=int((mags>thr).sum())
    Msn=best/math.sqrt(n)
    C=best/math.sqrt(n*math.log(p/n))
    print(f"{n:>5}{beta:>5}{p:>12}{Msn:>9.3f}{nlarge:>8}{Bcap:>9}{nlarge/Bcap:>11.5f}{C:>7.3f}")
