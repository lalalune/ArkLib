from sympy import primerange, primitive_root, symbols, factor
from collections import Counter
import numpy as np

def mu_n(p, n):
    g = primitive_root(p); h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]

def rEnergy(G, p, r):
    f = Counter({0: 1})
    for _ in range(r):
        f2 = Counter()
        for d, c in f.items():
            for s in G: f2[(d + s) % p] += c
        f = f2
    return sum(c * c for c in f.values())

# E_5 fit: leading (2*5-1)!! = 945. Need 5 points: n=4,8,16,32,64.
data=[]
for a in range(2,6):
    n=2**a
    target=n**8
    ps=[]
    for cc in primerange(target,target*10):
        if (cc-1)%n==0:
            ps.append(cc)
            if len(ps)>=2: break
    if len(ps)<2: print(f"n={n}: insufficient primes"); continue
    vals=[rEnergy(mu_n(p,n),p,5) for p in ps]
    consistent=len(set(vals))==1
    data.append((n,vals[0],consistent))
    print(f"n={n:<4} E5={vals[0]:<24} consistent={consistent}")

ns=np.array([d[0] for d in data],dtype=float)
E5s=np.array([d[1] for d in data],dtype=float)
diff=E5s-945*ns**5
A=np.vstack([ns**4,ns**3,ns**2,ns]).T
coef,res,_,_=np.linalg.lstsq(A,diff,rcond=None)
rc=[round(x) for x in coef]
print(f"\nE_5 = 945 n^5 + ({rc[0]}) n^4 + ({rc[1]}) n^3 + ({rc[2]}) n^2 + ({rc[3]}) n")
ok=all(abs(d[1]-(945*d[0]**5+rc[0]*d[0]**4+rc[1]*d[0]**3+rc[2]*d[0]**2+rc[3]*d[0]))<1 for d in data)
print("exact match all n:",ok)
n=symbols('n')
expr=945*n**5+rc[0]*n**4+rc[1]*n**3+rc[2]*n**2+rc[3]*n
print("E_5 factored:",factor(expr))
print("E_5/n factored:",factor(expr/n))

# Now examine the recurrence crossMass G r = E_{r+1} - n E_r for r=4: step target 2*4*(2*4-1)!! n^5 = 8*105 n^5 = 840 n^5
def E4(n): return 105*n**4-630*n**3+1435*n**2-1155*n
print("\nr=4 cross-step rung: crossMass G 4 = E_5 - n*E_4 <= 840 n^5 ?")
for d in data:
    n_=int(d[0]); cm=d[1]-n_*E4(n_)
    print(f"n={n_:<4} crossMass4={cm:<22} 840n^5={840*n_**5:<22} ratio={cm/(840*n_**5):.4f}")
