# Is the worst-b rep-set Sidon-floor THICKNESS-DEPENDENT? (brief rule 3 check)
# Compare additive energy of worst-b rep set W in THIN (beta~4) vs THICK (beta~2.3-3) regimes.
# If Sidon-floor holds in BOTH -> thickness-INVARIANT (honest caveat for the result).
import cmath,math
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
    vals=[]
    for j in range(m):
        b=pow(g,j,p)
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in mu)
        vals.append((abs(s),b))
    best=max(v for v,_ in vals); thr=(1-tau)*best
    return [b for v,b in vals if v>=thr],best
# find primes p = k*n+1 with beta = log(p)/log(n) near target
def find_prime(n,beta_target):
    import sympy
    target=int(round(n**beta_target))
    # p = k*n+1 near target
    k0=max(2,target//n)
    for k in range(k0,k0+20000):
        p=k*n+1
        if sympy.isprime(p):
            beta=math.log(p)/math.log(n)
            if abs(beta-beta_target)<0.25: return p,beta
    return None,None
try:
    import sympy
except ImportError:
    print("no sympy"); raise SystemExit
for n in (16,32):
    for beta in (2.4, 3.0, 4.0):
        p,b=find_prime(n,beta)
        if p is None: print(f"n={n} beta~{beta}: no prime"); continue
        g=primitive_root(p)
        Wb,best=worstb_repset(n,p,g,0.05)
        sz=len(Wb)
        if sz<3: print(f"n={n} beta={b:.2f} p={p}: |Wb|={sz} too small (M/sqrtn={best/math.sqrt(n):.2f})"); continue
        E=energy(Wb); floor=2*sz*sz-sz
        print(f"n={n} beta={b:.2f} p={p}: |Wb|={sz:3d} E={E} sidonFloor={floor} E/floor={E/floor:.3f} M/sqrtn={best/math.sqrt(n):.2f}")
