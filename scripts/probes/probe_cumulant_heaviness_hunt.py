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
def v2(m):
    v=0
    while m%2==0:m//=2;v+=1
    return v
def subgroup(p,n):
    for g0 in range(2,200):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return [pow(g,i,p) for i in range(n)],g0
    return None,None
def dfact(m):
    r=1;k=m
    while k>0:r*=k;k-=2
    return r
def maxrho(n,p,rmax):
    H,g0=subgroup(p,n)
    if H is None:return None,None
    tp=2*math.pi; f=(p-1)//n
    periods=[];rep=1;g=g0
    for j in range(f):
        c=0.0
        for x in H:c+=math.cos(tp*((rep*x)%p)/p)
        periods.append(c);rep=(rep*g)%p
    mr=0
    for r in range(1,rmax+1):
        Cr=n*sum(e**(2*r) for e in periods)
        mr=max(mr,Cr/(p*dfact(2*r-1)*(n**r)))
    M=max(abs(e) for e in periods)
    return mr,M
print("HEAVINESS HUNT — looking for ANY heavy prime at β≥3.5 (prize regime n/√p small)")
print(f"{'n':>4} {'p':>11} {'β':>5} {'n/√p':>7} {'v2(p-1)':>7} {'maxρ_r':>9} {'M/floor':>7} {'!':>5}")
found_heavy=False
for n in [64,128]:
    if n==128: betas=[4.0]
    else: betas=[2.7,3.0,3.3,3.6,4.0,4.5]
    for beta in betas:
        target=int(round(n**beta))
        # find several primes near target with VARIOUS 2-adic valuations (structured + generic)
        cands=[]
        # high 2-adic: p = a*2^t+1
        for t in range(v2(n), 32):
            for a in range(1, 200, 2):
                p=a*(1<<t)+1
                if target//3 < p < target*3 and (p-1)%n==0 and is_prime(p):
                    cands.append(p)
        cands=sorted(set(cands))[:14]
        for p in cands:
            if p>500_000_000: continue
            rmax=min(10,int(math.log(p))+2)
            mr,M=maxrho(n,p,rmax)
            if mr is None: continue
            nsp=n/math.sqrt(p);floor=math.sqrt(2*n*math.log(p))
            heavy = mr>1.15
            if heavy: found_heavy=True
            flag="HEAVY" if heavy else ""
            if heavy or p==cands[0] or v2(p-1)>=10:
                print(f"{n:>4} {p:>11} {math.log(p)/math.log(n):>5.2f} {nsp:>7.3f} {v2(p-1):>7} {mr:>9.2f} {M/floor:>7.2f} {flag:>5}",flush=True)
print("\nFOUND HEAVY at β≥3.5!" if found_heavy else "\nNO heavy prime found at β≥3.5 (all healthy) — supports conjecture")
