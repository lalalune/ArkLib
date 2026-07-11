import numpy as np, sympy
from itertools import product
from collections import Counter
# The DECISIVE provability test for the thin-regime telescoping lead:
# relative wraparound excess  rel_r = (E_r^p - E_r^0)/E_r^0  vs r, in the THIN prize regime (q=n^beta, beta~4).
# If rel_r stays SMALL (bounded, <1) up to r~log q => the energy bound E_r^p <= (1+rel)E_r^0 ~ Wick is provable-ish.
# If rel_r BLOWS UP at some r* < log q => the wraparound dominates = the open core.
def energies(n, p, r):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu_p=[pow(g,(m*s)%(p-1),p) for s in range(n)]          # n-th roots mod p
    roots_c=[np.exp(2j*np.pi*k/n) for k in range(n)]        # char-0
    c0=Counter(); cp=Counter()
    for tup in product(range(n),repeat=r):
        sc=sum(roots_c[j] for j in tup); c0[(round(sc.real,5),round(sc.imag,5))]+=1
        cp[sum(mu_p[j] for j in tup)%p]+=1
    E0=sum(v*v for v in c0.values()); Ep=sum(v*v for v in cp.values())
    return E0, Ep
print("rel_r = (E_r^p - E_r^0)/E_r^0  in the thin regime (beta=log_n p). Does it stay bounded to r~log q?")
for n in [8,16]:
    # pick primes spanning thin (beta ~ 3.5-5) ; log q (natural) ~ beta*ln n
    for p in [3329,12289,786433]:
        if (p-1)%n: continue
        beta=np.log(p)/np.log(n); lnq=np.log(p)
        rmax=min(7, 1+int(np.log(3_000_000)/np.log(n)))
        rels=[]
        for r in range(1,rmax+1):
            if n**r>3_000_000: break
            E0,Ep=energies(n,p,r)
            rels.append((r, (Ep-E0)/E0))
        relstr=" ".join(f"r{r}:{rl:+.3f}" for r,rl in rels)
        print(f"n={n} p={p} beta={beta:.2f} ln_q={lnq:.1f}(need r~{lnq:.0f}): {relstr}")
    print()
