# Refine: confirm E(W) ~ Sidon-floor (2|W|^2 - |W|) robustly, multiple primes & tau,
# and that W is energy-POOR vs random. Also recount antipodal pairs in W honestly.
import cmath,math,random
from collections import Counter
def subgroup(n,p,g):
    s=[];x=1
    for _ in range(n): s.append(x); x=x*g%p
    return s
def primitive_root(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None
def energy(W):
    c=Counter()
    for a in W:
        for b in W: c[a+b]+=1
    return sum(v*v for v in c.values())
def worstb_repset(n,p,g,tau):
    mu=subgroup(n,p,g); m=(p-1)//n
    vals=[];
    for j in range(m):
        b=pow(g,j,p)
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in mu)
        vals.append((abs(s),b))
    best=max(v for v,_ in vals)
    thr=(1-tau)*best
    # W as the set of WORST FREQUENCIES b (one per near-max coset rep), the door-iv object
    Wb=[b for v,b in vals if v>=thr]
    return Wb,best
for (n,p) in [(8,4153),(8,11593),(16,65617),(16,262193),(32,1048609)]:
    g=primitive_root(p)
    for tau in (0.02,0.05):
        Wb,best=worstb_repset(n,p,g,tau)
        sz=len(Wb)
        if sz<3:
            print(f"n={n} p={p} tau={tau}: |Wb|={sz} too small"); continue
        E=energy(Wb)
        sidonfloor=2*sz*sz-sz
        # antipodal count among reps
        Ws=set(Wb); anti=sum(1 for b in Wb if (p-b)%p in Ws)
        Es=[]
        for _ in range(6):
            R=random.sample(range(1,p),sz); Es.append(energy(R))
        Er=sum(Es)/len(Es)
        print(f"n={n} p={p} tau={tau}: |Wb|={sz:3d} E={E:6d} sidonFloor={sidonfloor:6d} E/floor={E/sidonfloor:.3f} E/rand={E/Er:.3f} antipodalReps={anti}")
