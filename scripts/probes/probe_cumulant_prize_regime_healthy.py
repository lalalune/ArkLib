import math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,target):
    p=target-(target%n)+1
    for d in range(0,20*n,n):
        if is_prime(p+d):return p+d
        if p-d>n and is_prime(p-d):return p-d
    return None
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return [pow(g,i,p) for i in range(n)],g0
def dfact(m):
    r=1;k=m
    while k>0:r*=k;k-=2
    return r
def analyze(n,p,rmax):
    H,g0=subgroup(p,n); tp=2*math.pi
    # eta_b constant on cosets b*mu_n. Iterate coset reps = powers of generator g0 step by n.
    # cosets: F_p* / mu_n, index f=(p-1)/n. rep_j = g0^j, j=0..f-1.
    f=(p-1)//n
    g=g0  # generator of F_p*
    # eta over coset rep r: sum_{x in H} cos(2π r x /p); each coset has n members same eta
    periods=[]
    rep=1
    for j in range(f):
        c=0.0
        for x in H: c+=math.cos(tp*((rep*x)%p)/p)
        periods.append(c)
        rep=(rep*g)%p
        if rep==1 and j<f-1: break  # safety
    res=[]
    for r in range(1,rmax+1):
        Cr=n*sum(e**(2*r) for e in periods)  # n members per coset
        res.append(Cr/(p*dfact(2*r-1)*(n**r)))
    M=max(abs(e) for e in periods)
    return res,M,len(periods),f
print("n=64 decisive: prize regime β≥4 (n/√p→0) vs owner's broken Fermat β=2.67")
for (label,target) in [("Fermat β≈2.67", 65537), ("β≈3", 64**3), ("PRIZE β=4", 64**4)]:
    n=64
    p=65537 if target==65537 else find_prime(n,target)
    if not p: print(f"  {label}: no prime"); continue
    if (p-1)%n!=0: print(f"  {label} p={p}: n∤p-1"); continue
    rmax=min(12,int(math.log(p))+2)
    res,M,npd,f=analyze(n,p,rmax)
    nsp=n/math.sqrt(p); floor=math.sqrt(2*n*math.log(p))
    mr=max(res)
    print(f"  {label}: p={p} β={math.log(p)/math.log(n):.2f} n/√p={nsp:.3f} f={f} maxρ={mr:.2f} M/√n={M/math.sqrt(n):.2f} M/floor={M/floor:.2f} {'HEAVY' if mr>1.1 else 'HEALTHY'}")
    print(f"      ρ_r:{['%.2f'%r for r in res]}", flush=True)
