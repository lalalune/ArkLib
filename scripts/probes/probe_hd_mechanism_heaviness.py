import math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    for q in (3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%m==0:continue
        x=pow(a,d,m);ok=(x==1)
        for _ in range(s):
            if x==m-1:ok=True;break
            x=x*x%m
        if not ok:return False
    return True
def factor(m):
    f={};d=2
    while d*d<=m:
        while m%d==0:f[d]=f.get(d,0)+1;m//=d
        d+=1
    if m>1:f[m]=f.get(m,0)+1
    return f
def largest_pf(m):
    return max(factor(m).keys()) if m>1 else 1
def smoothness(m):  # largest prime factor / m  (1=prime, small=smooth)
    return largest_pf(m)/m
def subgroup(p,n):
    for g0 in range(2,200):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return g0
def dfact(m):
    r=1;k=m
    while k>0:r*=k;k-=2
    return r
def maxrho(n,p,rmax):
    g0=subgroup(p,n)
    if not g0: return None
    H=[pow(g0,(p-1)//n*i,p) for i in range(n)]
    tp=2*math.pi;f=(p-1)//n;periods=[];rep=1
    for j in range(f):
        c=0.0
        for x in H:c+=math.cos(tp*((rep*x)%p)/p)
        periods.append(c);rep=(rep*g0)%p
    mr=max(n*sum(e**(2*r) for e in periods)/(p*dfact(2*r-1)*n**r) for r in range(1,rmax+1))
    return mr
print("HD-mechanism test (n=64): heaviness vs arithmetic structure of f=(p-1)/n, at SIMILAR n/√p")
print(f"{'p':>9} {'n/√p':>6} {'f=(p-1)/n':>10} {'f factored':>22} {'lpf(f)/f':>9} {'maxρ':>7} {'':>5}")
n=64
# collect primes in the heavy window n/√p in [0.15,0.35] => p in [64²/.35², 64²/.15²]=[33k,182k]
cands=[]
p=33000-(33000%n)+1
while p<185000:
    if is_prime(p) and (p-1)%n==0: cands.append(p)
    p+=n
import random
random.seed(1)
sample=cands  # all
rows=[]
for p in sample:
    mr=maxrho(n,p,9)
    if mr is None:continue
    f=(p-1)//n; nsp=n/math.sqrt(p)
    rows.append((p,nsp,f,mr))
# sort by smoothness of f
rows.sort(key=lambda r:smoothness(r[2]))
for (p,nsp,f,mr) in rows:
    if mr>1.15 or smoothness(f)<0.05 or smoothness(f)>0.5:  # show heavy + extremes of smoothness
        print(f"{p:>9} {nsp:>6.3f} {f:>10} {str(factor(f)):>22} {smoothness(f):>9.4f} {mr:>7.2f} {'HEAVY' if mr>1.15 else '':>5}",flush=True)
# correlation: among heavy vs healthy, compare smoothness
heavy=[r for r in rows if r[3]>1.15]; healthy=[r for r in rows if r[3]<=1.15]
import statistics
if heavy and healthy:
    print(f"\nHEAVY primes ({len(heavy)}): mean lpf(f)/f = {statistics.mean(smoothness(r[2]) for r in heavy):.4f} (smooth f ⟹ small)")
    print(f"HEALTHY primes ({len(healthy)}): mean lpf(f)/f = {statistics.mean(smoothness(r[2]) for r in healthy):.4f}")
