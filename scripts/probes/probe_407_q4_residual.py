import numpy as np
from itertools import product
import sympy
# THE IRREDUCIBLE RESIDUAL: Q4 = E_r(mu_n over F_p) - E_r^char0(mu_n over C).
# E_r = #{(x,y) in mu_n^{2r}: sum x = sum y}.  char0: equality in Z[zeta]; char-p: equality mod p.
# Q4 = wrap-around excess. The whole wall collapses to bounding p*Q4 - n^{2r} <= O((2n ln q)^r).
def er_char0_and_charp(n, r, p):
    # n-th roots of unity, exact in C (char0) and as residues mod p (char-p)
    roots_c = [np.exp(2j*np.pi*j/n) for j in range(n)]
    gg = sympy.primitive_root(p); w = pow(gg,(p-1)//n,p)
    roots_p = [pow(w,j,p) for j in range(n)]
    # enumerate r-tuples, bucket by sum (char0 rounded, char-p exact)
    from collections import Counter
    c0 = Counter(); cp = Counter()
    for tup in product(range(n), repeat=r):
        sc = sum(roots_c[j] for j in tup)
        c0[(round(sc.real,6), round(sc.imag,6))] += 1
        sp = sum(roots_p[j] for j in tup) % p
        cp[sp] += 1
    Er_c0 = sum(v*v for v in c0.values())
    Er_cp = sum(v*v for v in cp.values())
    return Er_c0, Er_cp
print("THE WRAP-AROUND RESIDUAL Q4 = E_r(F_p) - E_r(char0), and when it 'turns on'")
print(f"{'n':>3} {'r':>3} {'p':>7} {'beta':>5} {'E_r^char0':>10} {'E_r(F_p)':>10} {'Q4':>8} {'n^2r/p':>10}")
for n in [8, 16]:
    for r in range(2, 6):
        if n**r > 5_000_000: break
        for p in [97, 769, 12289, 786433]:  # increasing beta
            if (p-1) % n: continue
            beta = np.log(p)/np.log(n)
            if n**r > p*50 and n==16 and r>=5: continue
            try:
                e0, ep = er_char0_and_charp(n, r, p)
            except Exception as ex:
                continue
            q4 = ep - e0
            print(f"{n:>3} {r:>3} {p:>7} {beta:>5.2f} {e0:>10} {ep:>10} {q4:>8} {n**(2*r)/p:>10.1f}")
    print()
