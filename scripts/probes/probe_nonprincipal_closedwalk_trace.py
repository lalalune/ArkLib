import numpy as np
# Non-principal signed trace: sum_{b != 0} eta_b^k = q*W_k - n^k  (W_k = closed k-walks)
# and check the ODD-k structural sign-forcing: is it ever negative real? (phase-blind even can't be)
def test(p, n, k):
    G = sorted({x for x in range(1,p) if pow(x,n,p)==1})
    w = np.exp(2j*np.pi/p)
    eta = np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    full = np.sum(eta**k)
    nonprinc = full - eta[0]**k   # eta[0] = n
    # closed walks
    dist = np.zeros(p); dist[0]=1.0
    for _ in range(k):
        nd = np.zeros(p)
        for g in G: nd += np.roll(dist, g)
        dist = nd
    W = int(round(dist[0]))
    pred = p*W - n**k
    return nonprinc, pred

print("non-principal signed trace  Σ_{b≠0} η_b^k = q*W_k - n^k")
for (p,n) in [(257,16),(257,8),(73,9),(193,8)]:
    if (p-1)%n: 
        print(f"skip p={p} n={n}"); continue
    for k in [1,2,3,4,5]:
        np_val, pred = test(p,n,k)
        print(f"p={p:4d} n={n:3d} k={k}: Σ_nz η^k={np_val.real:+12.1f}{np_val.imag:+.1f}i  pred(qW-n^k)={pred:+12d}  match={abs(np_val-pred)<1e-3}  sign={'NEG' if np_val.real<-1e-6 else 'pos'}")
    print()
