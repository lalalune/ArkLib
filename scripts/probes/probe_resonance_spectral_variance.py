import cmath, math, random
random.seed(53)
def Khat(u,k,m): return sum(u[a]*cmath.exp(-2j*math.pi*a*k/m) for a in range(1,m))
import itertools
def phaseSum_all(u,r,m):
    P=[0j]*m; nz=[a for a in range(m) if a!=0]
    for X in itertools.product(nz,repeat=r):
        c=sum(X)%m; pr=1+0j
        for a in X: pr*=u[a]
        P[c]+=pr
    return P
def T(u,r,m): return sum(abs(v)**2 for v in phaseSum_all(u,r,m))
print("Spectral variance identity: (1/m)Σ_k(w_k-(m-1))² == T(2)-(m-1)² ? (w_k=|K̂(k)|²)")
for m in [3,5,7,11]:
    u=[0j]+[cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(m-1)]
    w=[abs(Khat(u,k,m))**2 for k in range(m)]
    var=sum((x-(m-1))**2 for x in w)/m
    rhs=T(u,2,m)-(m-1)**2
    print(f"  m={m}: var={var:.4f}  T(2)-(m-1)²={rhs:.4f}  diff={abs(var-rhs):.2e}  (var>=0 always)")
