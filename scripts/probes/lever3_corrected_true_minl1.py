import math
from itertools import combinations, product

# Compute the TRUE min l1 of a NONZERO vector c in Z^d with sum_k c_k g^k == 0 mod p.
# Enumerate by increasing l1 budget w: all nonzero integer vectors with sum|c_k|=w.
# (Meet-in-middle not needed for tiny d; brute by compositions.)
# This is the GENUINE lambda_1^{l1}(p0), distinct from the (buggy) trivial-walk girth.

def is_prime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
def prim_root(n,p):
    for g in range(2,p):
        if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return g
    return None

def true_min_l1(d,p,g,wmax=10):
    gp=[pow(g,k,p) for k in range(d)]
    # enumerate nonzero c with l1<=wmax by support size and signed magnitudes.
    # For efficiency: BFS over residue with state=(residue) tracking min l1 via Dijkstra
    # where each "move" adds +-g^k (cost 1). The min cost to return to 0 NONZERO is what we want.
    # The trivial-walk bug came from undirected-cycle detection; do it correctly:
    # min l1 nonzero vector = min over Dijkstra of (dist[r] + dist where you can also reach r
    # as the NEGATION-completion). Cleanest: Dijkstra dist[r]=min #signed-gen steps to reach r.
    # Then min nonzero l1 relation = min_r (dist[r] + dist[(p-r)%p]) over r in 1..p-1? No.
    # A nonzero relation sum c_k g^k=0 => the multiset of signed gens sums to 0. min steps to
    # write 0 as a NONEMPTY signed-gen sum. Split: pick first gen s (cost1) reaching residue s;
    # then min steps from s back to 0 = dist[(p-s)%p]... but that allows reusing -s to cancel
    # (giving c=0). To FORBID c=0 we need the relation to have nonzero NET coeffs. Equivalent
    # combinatorial fact: min l1 NONZERO = min_{s gen} 1 + dist_excluding_immediate_inverse.
    # Simplest correct approach for small p: Dijkstra dist (all = BFS since unit cost), then
    # min nonzero relation length = min over edges (u,s)->v of dist[u]+1+dist[v] where the
    # resulting coeff vector is checked nonzero by reconstruction. Instead, just BRUTE small w.
    import itertools
    for w in range(2, wmax+1):
        # all nonzero c with sum|c_k|=w: distribute w as sum of |c_k| over <= w supports
        # iterate over support subsets up to size min(w,d) and signed compositions
        found=False
        # choose support positions
        for supp_size in range(1, min(w,d)+1):
            for supp in combinations(range(d), supp_size):
                # compositions of w into supp_size positive parts
                # stars and bars
                for cut in combinations(range(1,w), supp_size-1):
                    parts=[]
                    prev=0
                    for c_ in cut: parts.append(c_-prev); prev=c_
                    parts.append(w-prev)
                    # assign signs
                    for signs in product([1,-1], repeat=supp_size):
                        val=sum(signs[i]*parts[i]*gp[supp[i]] for i in range(supp_size))%p
                        if val==0:
                            return w, [(supp[i], signs[i]*parts[i]) for i in range(supp_size)]
        # next w
    return None, None

n=16; d=8
print(f"n={n}, d={d}: TRUE min l1 of a NONZERO ideal vector (genuine lambda_1^l1):")
print("p          fermat?  true_min_l1  log_n(p)  witness")
for p in [4129, 4177, 4241, 4289, 65537, 65617, 65633]:
    if is_prime(p):
        g=prim_root(n,p)
        w,wit=true_min_l1(d,p,g,wmax=8)
        v2=0; m=p-1
        while m%2==0: v2+=1; m//=2
        fer = "FERMAT" if p==65537 else f"v2={v2}"
        print(f"{p:<10} {fer:<8} {str(w):<11} {math.log(p)/math.log(n):<9.3f} {wit}")
