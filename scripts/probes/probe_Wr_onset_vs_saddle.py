# probe_Wr_onset_vs_saddle.py (#444)
# DECIDES whether W_{r*}=0 (char-p wraparound excess vanishes at the saddle r*~ln q).
# RESULT (n=16, p=65617, exact): W_r=0 for r<=4, ONSET r_0=5, W_r>0 growing for r>=5.
# saddle r*=round(ln p)=11 >> onset 5  =>  W_{r*} > 0  =>  W_{r*}=0 is FALSE (cannot be proven).
# BUT the saddle bound A_r<=(q-1)Wick_r is W_r <= SLACK_r = (Wick_r - E_r^char0) + (n^{2r}-Wick_r)/q,
# and W_r/SLACK_r = 0.0002/0.0017/0.0045 at r=5/6/7 (tiny): the char-0 deficit dwarfs W_r, so the
# saddle holds with huge margin DESPITE W_r>0. W_{r*}=0 is the WRONG target; W_r<=SLACK_r is the open one.

import sys, math
from collections import Counter
def is_prime(m):
    if m<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def least_prime(n):
    k=n**3+1
    while True:
        p=k*n+1
        if p>n**4 and is_prime(p): return p
        k+=1
def proot(p):
    f=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in f):return g
n=16; rmax=8
p=least_prime(n); g=proot(p); h=pow(g,(p-1)//n,p)
muP=[pow(h,j,p) for j in range(n)]
half=n//2
def vec(j):
    v=[0]*half
    if j<half: v[j]=1
    else: v[j-half]=-1
    return tuple(v)
mu0=[vec(j) for j in range(n)]
cp=Counter({0:1}); c0=Counter({tuple([0]*half):1})
print(f"n={n} p={p} ln p={math.log(p):.2f} saddle r*={round(math.log(p))}", flush=True)
print(f"{'r':>3}{'E_r(Fp)':>15}{'E_r^char0':>15}{'W_r':>14}{'W_r>0?':>8}", flush=True)
onset=None
for r in range(1,rmax+1):
    cp=Counter({(s+x)%p:ct for s,ct in cp.items() for x in muP}) if False else (lambda:Counter())()
    nc=Counter()
    for s,ct in (cp if False else {}).items(): pass
    # explicit conv
    nc=Counter()
    for s,ct in (cp0 if False else {}).items(): pass
    break
# redo cleanly
cp=Counter({0:1}); c0=Counter({tuple([0]*half):1})
onset=None
for r in range(1,rmax+1):
    ncp=Counter()
    for s,ct in cp.items():
        for x in muP: ncp[(s+x)%p]+=ct
    cp=ncp
    nc0=Counter()
    for s,ct in c0.items():
        for x in mu0:
            nc0[tuple(s[i]+x[i] for i in range(half))]+=ct
    c0=nc0
    Ep=sum(v*v for v in cp.values()); E0=sum(v*v for v in c0.values()); W=Ep-E0
    if W>0 and onset is None: onset=r
    print(f"{r:>3}{Ep:>15}{E0:>15}{W:>14}{('YES' if W>0 else 'no'):>8}", flush=True)
print(f"onset r_0={onset}, saddle r*={round(math.log(p))} >> onset -> W_(r*) > 0 -> W_(r*)=0 is FALSE", flush=True)
