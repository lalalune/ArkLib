import cmath, itertools, math, random
random.seed(41)
def phaseSum_all(u, r, m):
    P=[0j]*m; nz=[a for a in range(m) if a!=0]
    for X in itertools.product(nz, repeat=r):
        c=sum(X)%m; pr=1+0j
        for a in X: pr*=u[a]
        P[c]+=pr
    return P
def T(u,r,m): return sum(abs(v)**2 for v in phaseSum_all(u,r,m))
print("Chebyshev lower bound: (m-1)*T(r) <= T(r+1) ?  + two-sided bracket vs (m-1)^2*T(r)")
viol=0; mn=1e9
for m in [3,5,7,11]:
    for trial in range(300):
        u=[0j]+[cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(m-1)]
        for r in [1,2,3]:
            lo=(m-1)*T(u,r,m); tr1=T(u,r+1,m); hi=(m-1)**2*T(u,r,m)
            mn=min(mn,tr1-lo)
            if tr1<lo-1e-7 or tr1>hi+1e-7: viol+=1
print(f"  violations of (m-1)T(r) <= T(r+1) <= (m-1)^2 T(r): {viol}  min lower-slack: {mn:.4f}")
# show a few bracket examples
print("  examples (m, r, lower=(m-1)T, T(r+1), upper=(m-1)^2 T):")
random.seed(1)
for m in [5,7]:
    u=[0j]+[cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(m-1)]
    for r in [1,2]:
        print(f"    m={m} r={r}: {(m-1)*T(u,r,m):8.2f} <= {T(u,r+1,m):8.2f} <= {(m-1)**2*T(u,r,m):8.2f}")
