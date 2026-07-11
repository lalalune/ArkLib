import numpy as np
# Probe: tr(A^3) = sum_b eta_b^3 = q * #{(x,y,z) in G^3 : x+y+z=0}
# for G = mu_n the n-th roots subgroup of F_q^*, q=p prime, p = 1 mod n.
def test(p, n):
    G = sorted({x for x in range(1,p) if pow(x,n,p)==1})
    assert len(G)==n, (len(G),n)
    assert 0 not in G
    w = np.exp(2j*np.pi/p)
    eta = np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    traceA3 = np.sum(eta**3)
    Gs=set(G)
    cnt=0
    for x in G:
        for y in G:
            z=(-x-y)%p
            if z in Gs: cnt+=1
    return traceA3, p*cnt, cnt

for (p,n) in [(11,5),(13,3),(31,5),(41,5),(43,7),(73,9),(127,7),(257,16)]:
    if (p-1)%n: continue
    t3, qcnt, cnt = test(p,n)
    print(f"p={p:4d} n={n:3d}: tr(A^3)={t3.real:+.3f}{t3.imag:+.3f}i  q*3walks={qcnt}  (3walks={cnt})  match={abs(t3-qcnt)<1e-6}")
