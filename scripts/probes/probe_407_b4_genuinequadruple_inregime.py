# B4 (dossier): is there char-p excess at r=2 at GENUINE prize primes (p~n^4, NOT Fermat)?
# E_2(mu_n) over F_p = #{(a,b,c,d) in mu_n^4 : a+b=c+d mod p}. char-0 value = 3n^2-3n (trivial: a=c,b=d OR a=d,b=c,
# minus overcount a=b=c=d). GenuineQuadruple <=> E_2 > char-0 value <=> char-p excess at r=2.
import math
def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%x==0:continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def v2(x):
    s=0
    while x%2==0:x//=2;s+=1
    return s
def fac(x):
    f={};dd=2
    while dd*dd<=x:
        while x%dd==0:f[dd]=f.get(dd,0)+1;x//=dd
        dd+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def E2(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    from collections import Counter
    # count sums a+b mod p, then E_2 = sum_s cnt[s]^2
    cnt=Counter()
    for a in mu:
        for b in mu: cnt[(a+b)%p]+=1
    return sum(c*c for c in cnt.values())
print("B4: E_2(mu_n) vs char-0 (3n^2-3n) at GENUINE prize primes p~n^4 (not Fermat). excess>0 => char-p r=2 excess",flush=True)
print(f"{'n':>4} {'p':>12} {'p=n^?':>6} {'E_2':>10} {'char0=3n^2-3n':>13} {'excess':>8}",flush=True)
for n in [16,32,64]:
    char0=3*n*n-3*n
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1; cnt=0
    while cnt<3 and p<3*lo:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if not isprime(p): continue
        e2=E2(p,n); logpn=math.log(p)/math.log(n)
        print(f"{n:>4} {p:>12} {logpn:>6.2f} {e2:>10} {char0:>13} {e2-char0:>8}",flush=True)
        cnt+=1
print("\nexcess=0 everywhere => r=2 char-p FAITHFUL in-regime (clean r=2 anchor; excess onset is r>=3+).",flush=True)
print("excess>0 => GenuineQuadruple true at genuine primes (char-p excess from r=2). DONE")
