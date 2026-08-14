import numpy as np, sympy
from itertools import product
from collections import Counter
# VALID provable lower bound: max^{2r} >= (q*E_r^char0 - n^{2r})/(q-1), E_r^char0 = TRUE char-0 energy (<= char-p E_r).
def er_char0(n, r):  # exact char-0 energy E_r of mu_n (= #{2r-tuples summing equal in C})
    roots=[np.exp(2j*np.pi/n*k) for k in range(n)]
    if n**r > 3_000_000: return None
    c=Counter()
    for tup in product(range(n), repeat=r):
        s=sum(roots[j] for j in tup); c[(round(s.real,5),round(s.imag,5))]+=1
    return sum(v*v for v in c.values())
def realperiods(p,n):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    return np.array([sum(np.exp(2j*np.pi*(b*x%p)/p) for x in mu).real for b in range(1,p)])
print(f"{'p':>8} {'n':>3} {'beta':>5} {'truemax':>8} {'sqrt(2n ln(q/n))':>15} {'PROVABLE-LB':>11} {'LB/sqrtn':>8} {'2sqrtn(Ram)':>11}")
for (p,n) in [(769,8),(12289,8),(786433,8),(769,16),(12289,16),(786433,16)]:
    if (p-1)%n: continue
    eta=realperiods(p,n); truemax=eta.max(); beta=np.log(p)/np.log(n)
    target=np.sqrt(2*n*np.log(p/n))
    best=0; bestr=0
    for r in range(1, 9):
        E=er_char0(n,r)
        if E is None: break
        num=p*E - n**(2*r)
        if num<=0: continue
        lb=(num/(p-1))**(1/(2*r))
        if lb>best: best=lb; bestr=r
    print(f"{p:>8} {n:>3} {beta:>5.2f} {truemax:>8.3f} {target:>15.3f} {best:>11.3f} {best/np.sqrt(n):>8.3f} {2*np.sqrt(n):>11.3f} (r*={bestr})")
