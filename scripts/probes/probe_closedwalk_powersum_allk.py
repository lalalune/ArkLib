import numpy as np
# General: sum_b eta_b^k = q * #{(x_1..x_k) in G^k : sum x_i = 0}
def test(p, n, k):
    G = sorted({x for x in range(1,p) if pow(x,n,p)==1})
    assert len(G)==n
    w = np.exp(2j*np.pi/p)
    eta = np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    sk = np.sum(eta**k)
    # count k-tuples summing to 0 via DP over residues
    from itertools import product
    # DP
    dist = np.zeros(p)
    dist[0]=1.0
    for _ in range(k):
        nd = np.zeros(p)
        for g in G:
            nd += np.roll(dist, g)
        dist = nd
    cnt = int(round(dist[0]))
    return sk, p*cnt, cnt

for (p,n) in [(41,5),(73,9),(257,16),(257,8)]:
    for k in [1,2,3,4,5]:
        sk, qcnt, cnt = test(p,n,k)
        nonneg = sk.real >= -1e-6
        print(f"p={p:4d} n={n:3d} k={k}: S_k={sk.real:+10.2f}{sk.imag:+.2f}i  q*cnt={qcnt:8d}  match={abs(sk-qcnt)<1e-4}  nonneg={nonneg}")
    print()
