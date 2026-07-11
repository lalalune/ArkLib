import numpy as np
from itertools import product
from collections import Counter
import sympy
# Pin the EXACT depth threshold r* where Q4 turns on (Q4=0 for r<r*).
def q4(n, r, p):
    roots_c = [np.exp(2j*np.pi*j/n) for j in range(n)]
    gg = sympy.primitive_root(p); w = pow(gg,(p-1)//n,p)
    roots_p = [pow(w,j,p) for j in range(n)]
    c0=Counter(); cp=Counter()
    for tup in product(range(n),repeat=r):
        sc=sum(roots_c[j] for j in tup); c0[(round(sc.real,5),round(sc.imag,5))]+=1
        cp[sum(roots_p[j] for j in tup)%p]+=1
    return sum(v*v for v in cp.values()) - sum(v*v for v in c0.values())
print("EXACT threshold r* (Q4=0 for r<r*) vs beta=log_n(p).  Hypothesis: r* ~ beta (height = r*log... )")
print(f"{'n':>3} {'p':>8} {'beta':>5}   r: " + " ".join(f"{r}" for r in range(2,7)))
for n in [8,16]:
    for p in [97,193,257,769,3329,12289,40961,786433]:
        if (p-1)%n: continue
        beta=np.log(p)/np.log(n)
        row=[]
        for r in range(2,7):
            if n**r>4_000_000: row.append('-'); continue
            row.append('0' if q4(n,r,p)==0 else 'X')
        # r* = first X
        rstar = next((r for r,v in zip(range(2,7),row) if v=='X'), None)
        print(f"{n:>3} {p:>8} {beta:>5.2f}   {' '.join(f'{v:>1}' for v in row)}    r*={rstar}  (beta+1={beta+1:.1f})")
