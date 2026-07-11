import itertools, random
def isprime(x):
    if x<2:return False
    for d in range(2,int(x**0.5)+1):
        if x%d==0:return False
    return True
def proot(p):
    def order(a):
        o=1;x=a%p
        while x!=1:x=x*a%p;o+=1
        return o
    for g in range(2,p):
        if order(g)==p-1:return g
def setup(n,plo):
    p=plo
    while not(p%n==1 and isprime(p)):p+=1
    g=proot(p);h=pow(g,(p-1)//n,p)
    return p,[pow(h,i,p) for i in range(n)]
def ddk(vals,pts,k,p):
    xs=pts[:k+1];vs=list(vals[:k+1])
    for j in range(1,k+1):
        for i in range(k,j-1,-1):
            vs[i]=(vs[i]-vs[i-1])*pow((xs[i]-xs[i-j])%p,p-2,p)%p
    return vs[k]
def in_RS(vals,pts,k,p):
    s=len(pts)
    if s<=k:return True
    for st in range(s-k):
        if ddk(vals[st:st+k+1],pts[st:st+k+1],k,p)!=0:return False
    return True
def incidence(u0,u1,n,mu,k,p,r,combos):
    gam=set()
    for R in combos:
        pts=[mu[i] for i in R];u0R=[u0[i] for i in R];u1R=[u1[i] for i in R]
        if in_RS(u1R,pts,k,p):
            if in_RS(u0R,pts,k,p):return p
            continue
        a0=ddk(u0R,pts,k,p);a1=ddk(u1R,pts,k,p)
        if a1%p==0:continue
        g=(-a0*pow(a1,p-2,p))%p
        if in_RS([(u0R[i]+g*u1R[i])%p for i in range(len(R))],pts,k,p):gam.add(g)
    return len(gam)
n=16;k=4;r=10
p,mu=setup(n,200000)
combos=list(itertools.combinations(range(n),n-r))
def mv(b):return [pow(x,b,p) for x in mu]
# monomial best (full)
monbest=0;monarg=None
for a in range(k,n):
    for b in range(k,n):
        if a==b:continue
        I=incidence(mv(a),mv(b),n,mu,k,p,r,combos)
        if I<p and I>monbest:monbest=I;monarg=(a,b)
print(f"p={p} MONO best={monbest} at {monarg}",flush=True)
# structured: perturb winning direction + random structured, FOCUSED (~250 dirs)
sbest=0;sarg=None;random.seed(3);cnt=0
cands=[]
# 2-term u1 around b=4, u0=x^10 and around
for b2 in range(k,n):
    for c in [1,2,p-1,p-2]:
        cands.append(('p',10,4,b2,c))
# random structured: u0,u1 random low-degree-combos of <=3 monomials
for _ in range(150):
    es=random.sample(range(k,n),3); cs=[random.randrange(1,p) for _ in range(3)]
    es2=random.sample(range(k,n),3); cs2=[random.randrange(1,p) for _ in range(3)]
    cands.append(('r',es,cs,es2,cs2))
for cand in cands:
    if cand[0]=='p':
        _,a,b,b2,c=cand
        u0=mv(a);u1=[(pow(x,b,p)+c*pow(x,b2,p))%p for x in mu]
    else:
        _,es,cs,es2,cs2=cand
        u0=[sum(cs[j]*pow(x,es[j],p) for j in range(3))%p for x in mu]
        u1=[sum(cs2[j]*pow(x,es2[j],p) for j in range(3))%p for x in mu]
    I=incidence(u0,u1,n,mu,k,p,r,combos);cnt+=1
    if I<p and I>sbest:sbest=I;sarg=cand
print(f"STRUCT best={sbest} ({cnt} dirs) {'BEATS' if sbest>monbest else 'does NOT beat'} mono {monbest}",flush=True)
print("escape-viable" if sbest<=monbest else "general/structured exceeds => wall",flush=True)
print("DONE")
