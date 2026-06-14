import sympy, random
from collections import Counter
from itertools import product

def subgroup(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

def E3(H,p):
    c=Counter()
    for t in product(H,repeat=3): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

def is_sidon(H,p):
    s=set()
    for i in range(len(H)):
        for j in range(i+1,len(H)):
            d=(H[i]+H[j])%p
            if d in s: return False
            s.add(d)
    return True

# REFUTATION CHECK for C8: is E_3=6n^3-9n^2+4n special to mu_p, or generic to ANY Sidon set?
print("C8 refutation check: E_3 of mu_p vs RANDOM Sidon set of same size. If equal => generic, not special.")
print(f"{'n=p':>4} {'E3(mu_p)':>9} {'6n^3-9n^2+4n':>13} {'E3(rand Sidon)':>15} {'match formula?':>14}")
for p in [3,5,7,11,13]:
    H,P=subgroup(p)
    e_mu=E3(H,P)
    formula=6*p**3-9*p**2+4*p
    # random Sidon set of size p in a large field
    q=sympy.nextprime(p*p*50)
    random.seed(p)
    R=None
    for _ in range(200):
        cand=random.sample(range(1,q), p)
        if is_sidon(cand,q): R=cand; break
    e_rand = E3(R,q) if R else None
    print(f"{p:>4} {e_mu:>9} {formula:>13} {str(e_rand):>15} {str(e_mu==formula):>14}")
print("\nIf E3(rand Sidon) != formula but E3(mu_p)==formula => C8 is SPECIAL to mu_p (genuine new result).")
print("If E3(rand Sidon)==formula => C8 is the generic Sidon 3-energy (still a valid closed form, less novel).")
