import cmath, itertools, math, random
random.seed(17)
def phaseSum_all(u, r, m):
    P=[0j]*m; nz=[a for a in range(m) if a!=0]
    for X in itertools.product(nz, repeat=r):
        c=sum(X)%m; pr=1+0j
        for a in X: pr*=u[a]
        P[c]+=pr
    return P
def T(u,r,m): return sum(abs(v)**2 for v in phaseSum_all(u,r,m))
# stdAddChar(x) = exp(2 pi i x / m). dftChar_k(c)=stdAddChar(-(c k)) = exp(-2 pi i c k/m).
# K_hat(k) = sum_{a!=0} u(a) dftChar_k(a) = sum_{a!=0} u(a) exp(-2 pi i a k/m).
def Khat(u,k,m): return sum(u[a]*cmath.exp(-2j*math.pi*a*k/m) for a in range(1,m))
print("Parseval bridge: m*T(r) == sum_k |K_hat(k)|^{2r} ?")
maxerr=0.0
for m in [3,5,7]:
    u=[0j]+[cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(m-1)]
    for r in [1,2,3]:
        lhs=m*T(u,r,m)
        rhs=sum(abs(Khat(u,k,m))**(2*r) for k in range(m))
        maxerr=max(maxerr,abs(lhs-rhs))
        print(f"  m={m} r={r}: m*T(r)={lhs:10.4f}  sum_k|K|^2r={rhs:10.4f}  diff={abs(lhs-rhs):.2e}")
print(f"  max error: {maxerr:.2e} (machine epsilon => bridge EXACT)")
