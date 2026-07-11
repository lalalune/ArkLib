import itertools, sympy
from collections import Counter

def mu_n(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, k, p) for k in range(n)})

# check  max_t #{w in G^r : sum w = t}  <=  |G|^(r-1)
for (n, p) in [(4,4001),(8,8009)]:
    G = mu_n(p,n)
    for r in range(1,5):
        cnt = Counter()
        for w in itertools.product(G, repeat=r):
            cnt[sum(w)%p]+=1
        mx = max(cnt.values())
        print(f"n={n} r={r}: max fiber={mx}  |G|^(r-1)={n**(r-1)}  ok={mx<=n**(r-1)}")
