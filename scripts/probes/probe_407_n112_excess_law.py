import numpy as np, sympy
from itertools import combinations
from math import comb
# The localized core: at |R|=2t (binding ~n/2), char-p vanishing-2t-subset count of mu_n vs char-0 count.
# char-0 vanishing 2t-subsets = unions of t antipodal pairs (Lam-Leung) = C(n/2, t).
# char-p: subsets S, |S|=2t, with sum_{s in S} s ≡ 0 mod p. Excess = char-p count - char-0 count.
def counts(n, p, t):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]  # n-th roots mod p
    w=2*t
    char0 = comb(n//2, t)  # unions of t antipodal pairs
    cp=0
    # enumerate w-subsets (feasible only small n,w)
    for S in combinations(range(n), w):
        if sum(mu[i] for i in S)%p==0: cp+=1
    return char0, cp
# height H(n) ~ field norm of a binding vanishing sum; crossover where p ~ H(n)
print(f"{'n':>3} {'t':>3} {'w':>3} {'p':>8} {'beta':>5} {'char0=C(n/2,t)':>14} {'char-p':>8} {'excess':>8}")
for n in [12,16]:
    for t in [2,3,n//4]:
        w=2*t
        if comb(n,w)>2_000_000: continue
        for p in [97,193,769,3329,12289]:
            if (p-1)%n: continue
            beta=np.log(p)/np.log(n)
            try: c0,cp=counts(n,p,t)
            except: continue
            print(f"{n:>3} {t:>3} {w:>3} {p:>8} {beta:>5.2f} {c0:>14} {cp:>8} {cp-c0:>8}")
    print()
