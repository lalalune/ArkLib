import sympy
from collections import Counter
from itertools import product

def subgroup(n):
    # generic prime p>P_max so mu_n behaves as over C
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            H=[pow(z,j,p) for j in range(n)]
            return H,p

def E_plus(H,p):  # 4-var additive energy
    c=Counter()
    for a in H:
        for b in H: c[(a+b)%p]+=1
    return sum(v*v for v in c.values())

def sumset(H,p): return len({(a+b)%p for a in H for b in H})
def diffset(H,p): return len({(a-b)%p for a in H for b in H})

def E3(H,p):  # 6-var additive energy
    c=Counter()
    for t in product(H,repeat=3): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

print("Conjecture batch 1 — additive structure of mu_n. Refute by mismatch with proposed closed form.")
print(f"{'n':>3} {'par':>4} {'E+':>7} {'conjE+':>7} {'|H+H|':>6} {'conjSS':>7} {'|H-H|':>6} {'E3':>9} {'conjE3':>9}")
for n in [3,5,7,9,11,13,15, 4,8,16,32, 6,12,10]:
    H,p=subgroup(n)
    Ep=E_plus(H,p); ss=sumset(H,p); ds=diffset(H,p)
    # CONJECTURES:
    cEp = (3*n*n-3*n) if n%2==0 else (2*n*n-n)         # C1: energy closed form
    cSS = ((n*n+2)//2) if n%2==0 else ((n*n+1)//2)     # C6: sumset (even: (n^2+2)/2)
    E3v = E3(H,p) if n<=16 else 0
    cE3 = (15*n**3 - 0) if False else None             # placeholder, learn from data
    print(f"{n:>3} {'even' if n%2==0 else 'odd':>4} {Ep:>7} {cEp:>7} {ss:>6} {cSS:>7} {ds:>6} {E3v:>9} {'?':>9}")
print("\nC1 (E+): survives if E+ matches conjE+. C6 (sumset): survives if |H+H| matches conjSS.")
print("Note |H-H| for diffset; E3 for next conjecture calibration.")
