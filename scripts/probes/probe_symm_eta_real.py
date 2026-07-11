import numpy as np
# When -G=G, eta_b = sum_{x in G} psi(b x) is REAL (x and -x conjugate-pair).
# Then eta_b^{2r} = |eta_b|^{2r} (real, even power nonneg), so the un-conjugated
# even trace EQUALS the conjugated even moment.
for (p,n) in [(257,16),(257,8),(193,8),(73,9)]:
    if (p-1)%n: continue
    G=sorted({x for x in range(1,p) if pow(x,n,p)==1})
    symm = set((-np.array(G))%p)==set(G)
    w=np.exp(2j*np.pi/p)
    eta=np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    maximg=np.max(np.abs(eta.imag))
    # check eta^{2r} == |eta|^{2r}
    ok2 = np.allclose(eta**2, np.abs(eta)**2, atol=1e-6)
    print(f"p={p} n={n} (-G=G:{symm}): max|Im eta|={maximg:.2e}  eta^2==|eta|^2: {ok2}")
