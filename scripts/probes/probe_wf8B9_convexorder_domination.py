import math
from fractions import Fraction as Fr

# CHAR-P period law: eta_b = sum_{x in mu_n} e_p(b x), b over nonzero cosets. mu_n = subgroup of order n.
# E_r^{charp} := (1/m) sum_{b!=0 cosets} eta_b^{2r}   (m = #cosets = (p-1)/n)
# Compare to char-0 random-walk moment A_r (sum of n uniform phasors).
# CONVEX-ORDER CLAIM (B9 deliverable): char-p law <=_cx char-0 random-walk law
#   <=>  E_r^{charp}/m_charp  <= A_r  for all r ?   Actually need same variance normalization.
# char-p second moment: E_1^{charp} = (1/m) sum eta_b^2. Over nonzero cosets, sum_{b!=0} eta_b^2 = ?
# We'll just compute Wick-normalized m_r^{charp} = E_r^{charp}/((2r-1)!! n^r) and compare to char0 m_r.
import cmath
def mpow(a,e,p):
    r=1; a%=p
    while e>0:
        if e&1: r=r*a%p
        a=a*a%p; e>>=1
    return r
def isp(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def find_p(n, lo):
    p = lo + ((1+n-lo%n)%n)
    if p<=2: p+=n
    while True:
        if p>2 and p%n==1 and isp(p): return p
        p+=n
def proot(p):
    m=p-1; fs=[]; d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.append(m)
    g=2
    while True:
        if all(mpow(g,(p-1)//f,p)!=1 for f in fs): return g
        g+=1

def coeff_I0pow(n, r):
    base=[Fr(1,math.factorial(k)**2) for k in range(r+1)]
    poly=[Fr(0)]*(r+1); poly[0]=Fr(1)
    for _ in range(n):
        new=[Fr(0)]*(r+1)
        for i in range(r+1):
            if poly[i]==0: continue
            for k in range(r+1-i):
                new[i+k]+=poly[i]*base[k]
        poly=new
    return poly[r]
def A_r(n,r): return float(Fr(math.factorial(r))**2*coeff_I0pow(n,r))
def dfo(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v

def run(n, beta, rmax):
    p=find_p(n, int(n**beta))
    g=proot(p); h=mpow(g,(p-1)//n,p)
    mu=[mpow(h,j,p) for j in range(n)]
    m=(p-1)//n; gn=mpow(g,n,p)
    eta=[]; b=1
    for _ in range(m):
        re=0.0
        for x in mu:
            t=(b*x)%p
            re+=math.cos(2*math.pi*t/p)
        eta.append(re); b=(b*gn)%p
    print(f"-- n={n} p={p} beta~{math.log(p)/math.log(n):.2f} lnq={math.log(p):.1f} r*~{math.log(p)/2:.0f} --")
    print("   r   m_r^charp   m_r^char0   charp<=char0?  (convex-order domination by random-walk law)")
    for r in range(1,rmax+1):
        s=sum(e**(2*r) for e in eta)
        Er=s/m
        wick=dfo(r)*n**r
        mcp=Er/wick
        mc0=A_r(n,r)/wick
        print(f"  {r:3d}  {mcp:9.4f}   {mc0:9.4f}    {'YES' if mcp<=mc0+1e-9 else 'NO '}")
run(16, 4.0, 14)
run(32, 4.0, 16)
run(64, 4.0, 18)
