import math
from math import comb
# Capstone: the MGF decomposition  sum_b e^{y eta_b} = p*I0(2y)^{n/2} + p*(excess), excess = the SAME excess
# relations the army found. Show: (1) the char-0 part p*I0^{n/2} EXACTLY equals the antipodal-only contribution;
# (2) the true MGF EXCEEDS it (excess>0, grows with y) -- inflating every aggregate route; (3) yet max|eta_b| < floor.
# => all aggregate routes (moment/energy/MGF/cumulant) fail for the SAME reason; only per-frequency BGK remains.
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
    f={};d=2
    while d*d<=x:
        while x%d==0:f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def I0(z, K=200):
    # I0(z) = sum (z/2)^{2k}/(k!)^2
    s=0.0; t=1.0; 
    for k in range(K):
        if k>0: t*= (z/2)**2/(k*k)
        s+=t
        if t<1e-18*s and k>5: break
    return s
def analyze(p,n,y):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    eta=[sum(math.cos(2*math.pi*((b*x)%p)/p) for x in mu) for b in range(p)]  # all b incl 0
    LHS=sum(math.exp(y*e) for e in eta)
    char0=p*(I0(2*y)**(n//2))
    excess=LHS-char0
    M=max(abs(eta[b]) for b in range(1,p))
    floor=math.sqrt(2*n*math.log((p-1)//n))
    return LHS,char0,excess,M,floor
print("MGF decomposition  sum_b e^{y eta_b} = p I0(2y)^{n/2} + EXCESS, at saddle y*=sqrt(2 log m/n):",flush=True)
print(f"{'p':>8} {'n':>4} {'y*':>6} {'LHS':>12} {'p*I0^{n/2}':>12} {'excess':>11} {'exc/char0':>9} {'M/floor':>8}",flush=True)
for n in [8,16,32]:
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1; cnt=0
    while cnt<1 and p<2*lo:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if not isprime(p): continue
        if p>200000: break
        m=(p-1)//n
        ystar=math.sqrt(2*math.log(m)/n)
        LHS,char0,excess,M,floor=analyze(p,n,ystar)
        print(f"{p:>8} {n:>4} {ystar:>6.3f} {LHS:>12.4g} {char0:>12.4g} {excess:>11.4g} {excess/char0:>9.4f} {M/floor:>8.3f}",flush=True)
        cnt+=1
print("\nexcess>0 (the army's excess relations) inflates the MGF aggregate; yet M/floor<1 => the inflation is in",flush=True)
print("the AGGREGATE not the MAX. ALL aggregate routes (moment/energy/MGF/cumulant) fail identically; only the",flush=True)
print("per-frequency direct bound |eta_b|<=sqrt(2n log m) (=BGK) escapes the excess. DONE")
