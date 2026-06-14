# Verify the squaring-descent induction for m=2 on gap-valid S over F_p.
# S subset mu_n (n=2^mu), e1(S)=e3(S)=0 (mod p).  Decompose via x->x^2:
#   c_w = #{x in S: x^2=w} in {0,1,2}.  D2={w:c_w=2} (paired), U={x in S: c_{x^2}=1} (single).
# CLAIMS: (1) e1(U)=e3(U)=0 (U is a smaller gap-valid config) ;
#         (2) e2(S) = e2(U) - sum_{w in D2} w ;
#         (3) e2(S) in Sigma_r  (sum of r distinct mu_{n/2} elts).
from itertools import combinations
import sympy as sp

def esym(pts, i, p):           # e_i of a list of field elts, mod p
    s=0
    for c in combinations(pts,i):
        prod=1
        for x in c: prod=(prod*x)%p
        s=(s+prod)%p
    return s%p

def run(n,m,r,p):
    assert m==2
    # primitive n-th root g in F_p
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,n//2,p)==p-1: g=gg;break
    mun=[pow(g,j,p) for j in range(n)]                 # mu_n as field elts
    munhalf=[pow(g,2*j,p) for j in range(n//2)]        # mu_{n/2}
    size=2*r; gap=[1,3]
    # genuine sumset Sigma_r mod p
    Sigma=set()
    for W in combinations(munhalf, r):
        Sigma.add(sum(W)%p)
    checked=0; spurious=0; claim1=claim2=claim3=0; both=0
    for Sidx in combinations(range(n), size):
        S=[mun[j] for j in Sidx]
        if esym(S,1,p)!=0 or esym(S,3,p)!=0: continue
        checked+=1
        # squaring decomposition
        sq={}
        for x in S:
            w=(x*x)%p; sq.setdefault(w,[]).append(x)
        D2=[w for w,xs in sq.items() if len(xs)==2]
        U =[xs[0] for w,xs in sq.items() if len(xs)==1]
        is_coset = (len(U)==0)
        if not is_coset: spurious+=1
        # CLAIM 1: e1(U)=e3(U)=0
        c1 = (esym(U,1,p)==0 and esym(U,3,p)==0)
        # CLAIM 2: e2(S) == e2(U) - sum_{D2} w
        lhs=esym(S,2,p); rhs=(esym(U,2,p) - sum(D2))%p
        c2 = (lhs%p==rhs%p)
        # CLAIM 3: e2(S) in Sigma_r
        c3 = (esym(S,2,p)%p in Sigma)
        claim1+=c1; claim2+=c2; claim3+=c3
        if c1 and c2 and c3: both+=1
    print(f"n={n} r={r} p={p}: gap-valid={checked} (spurious non-coset={spurious}) | "
          f"CLAIM1 e1=e3=0 on U: {claim1}/{checked} | CLAIM2 e2 formula: {claim2}/{checked} | "
          f"CLAIM3 e2 in Sigma: {claim3}/{checked} | all3: {both}/{checked}")

# pick primes ===1 mod n where spurious appear
for (n,r) in [(16,4),(16,3)]:
    for p in sp.primerange(17, 400):
        if p%n==1:
            run(n,2,r,p)
