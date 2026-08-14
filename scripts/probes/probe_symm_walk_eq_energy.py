import numpy as np
# W_{2r} = #{(x_1..x_{2r}) in G^{2r}: sum=0}   (closed 2r-walk, un-conjugated)
# E_r    = #{(v,w) in (G^r)^2 : sum v = sum w}  (conjugated additive energy)
# Claim to test: W_{2r} relates to E_r how?  For a SYMMETRIC set (-G=G) we expect
#   W_{2r} = #{(v,w): sum v + sum w = 0} = #{(v,w): sum v = -sum w} = #{(v,w'): sum v = sum w'}
#   under w'_i = -w_i (bijection G^r->G^r iff -G=G), so W_{2r} = E_r exactly when -G=G.
def walks(G,p,k):
    dist=np.zeros(p); dist[0]=1.0
    for _ in range(k):
        nd=np.zeros(p)
        for g in G: nd+=np.roll(dist,g)
        dist=nd
    return int(round(dist[0]))
def energy(G,p,r):
    # #{(v,w): sum v = sum w}, via convolution: count_r[s]=#{v in G^r: sum=s}; E=sum_s count_r[s]^2
    cnt=np.zeros(p); cnt[0]=1.0
    for _ in range(r):
        nd=np.zeros(p)
        for g in G: nd+=np.roll(cnt,g)
        cnt=nd
    return int(round(np.sum(cnt*cnt)))
for (p,n) in [(257,16),(257,8),(193,8),(73,9),(41,5)]:
    if (p-1)%n: continue
    G=sorted({x for x in range(1,p) if pow(x,n,p)==1})
    symm = set((-np.array(G))%p)==set(G)
    print(f"p={p} n={n} (-G=G:{symm}):")
    for r in [1,2,3]:
        W=walks(G,p,2*r); E=energy(G,p,r)
        print(f"   r={r}: W_2r={W:8d}  E_r={E:8d}  equal={W==E}")
