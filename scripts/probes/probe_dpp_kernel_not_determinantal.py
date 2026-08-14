import numpy as np
from math import sqrt, log
exec(open('saturate.py').read().split('print("SATURATE')[0])  # helpers is_prime, primroot

def eta_all(p,n):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    roots=np.array([pow(w,i,p) for i in range(n)],dtype=np.int64)
    b=np.arange(p,dtype=np.int64)
    out=np.empty(p,dtype=complex)
    BL=20000
    for i in range(0,p,BL):
        bb=np.arange(i,min(i+BL,p),dtype=np.int64)[:,None]
        out[i:i+bb.shape[0]]=np.exp(2j*np.pi*((bb*roots[None,:])%p)/p).sum(axis=1)
    return out

print("DPP test: is the period family a rich determinantal point process (low-rank kernel ⟹ provable")
print("sub-Gaussian max, phase-FREE) or just iid-with-one-constraint (negligible negative correlation)?")
print("="*72)
for n,p in [(16,257),(16,65537),(32,1048609)]:
    if (p-1)%n!=0 or not is_prime(p): continue
    eta=eta_all(p,n)
    X=np.abs(eta[1:])**2   # |eta_b|^2 over b!=0
    mu=X.mean(); var=X.var()
    # the covariance structure: is Cov(X_a,X_b) = -var/(m-1) distance-indep (single constraint = ~iid)
    # or a rich kernel? Test: empirical lag-correlations should be ~ -1/(m-1) flat if single-constraint
    m=p-1
    # measure autocovariance at a few lags (in the b-index, but b is unordered; use random pairs)
    rng=np.random.default_rng(0)
    pairs=rng.integers(1,p,size=(5000,2))
    pairs=pairs[pairs[:,0]!=pairs[:,1]]
    cov_emp=np.mean((np.abs(eta[pairs[:,0]])**2-mu)*(np.abs(eta[pairs[:,1]])**2-mu))
    cov_pred=-var/(m-1)   # single-constraint exchangeable prediction
    print(f"n={n:3d} p={p:8d}: mean|eta|²={mu:.3f}(=n? {n}) var={var:.2f}")
    print(f"   off-diag Cov(|eta_a|²,|eta_b|²): empirical={cov_emp:.4f}  single-constraint pred={cov_pred:.6f}  "
          f"ratio={cov_emp/cov_pred:.2f}")
    print(f"   ⟹ {'~single-constraint (≈iid, neg-corr O(1/m) NEGLIGIBLE ⟹ DPP gives nothing beyond iid)' if abs(cov_emp)<10*abs(cov_pred) else 'RICH kernel (DPP structure!)'}")
print()
print("VERDICT: if Cov ~ -var/(m-1) (single linear constraint Σeta_b=-n), the family is iid-with-one-")
print("constraint; the negative correlation is O(1/m)~O(n/p) NEGLIGIBLE ⟹ no rich DPP kernel ⟹ the DPP")
print("route gives only the iid extreme value (C_iid→1), NOT a phase-free sub-√n bound. Reduces to iid.")
