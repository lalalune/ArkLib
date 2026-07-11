import numpy as np
# For symmetric G (-G=G), study odd closed-walk counts W_{2r+1} and the eta_{-b}=eta_b structure.
# Question: is there a clean structural identity for W_odd on symmetric G?
# Also: eta_{-b} = eta_b (real & even in b). Does that force W_k relation?
def walks(G,p,k):
    dist=np.zeros(p); dist[0]=1.0
    for _ in range(k):
        nd=np.zeros(p)
        for g in G: nd+=np.roll(dist,g)
        dist=nd
    return int(round(dist[0]))
for (p,n) in [(257,16),(257,8),(193,8),(97,16)]:
    if (p-1)%n: continue
    G=sorted({x for x in range(1,p) if pow(x,n,p)==1})
    symm = set((-np.array(G))%p)==set(G)
    w=np.exp(2j*np.pi/p)
    eta=np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    # check eta_{-b}=eta_b
    even_in_b = all(abs(eta[(-b)%p]-eta[b])<1e-9 for b in range(p))
    print(f"p={p} n={n} symm={symm} eta_even_in_b={even_in_b}")
    for k in [1,2,3,4,5,6,7]:
        print(f"   W_{k}={walks(G,p,k)}")
