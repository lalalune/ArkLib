import numpy as np
from sympy import isprime, primitive_root
from collections import Counter

# Does the shallow-r A_r>Wick violation affect the OPTIMIZED certificate min_r (q*Wick_r)^{1/2r}
# as an UPPER bound for M? I.e. if we use Wick as a SURROGATE for A_r (the conditional bound),
# at p=1217 is min_r (q*Wick_r)^{1/2r} still >= true M? If A_2>Wick_2, then (q*Wick_2)^{1/4} is
# NOT a valid upper bound at r=2 (since q*A_2 > q*Wick_2 and q*A_2 >= |eta_max|^4)... let's check
# whether the true max |eta|^2 exceeds (q*Wick_r)^{1/r} at the violating r.

def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def analyze(n,p):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=[pow(gen,j,p) for j in range(n)]
    a2=np.array([abs(np.exp(2j*np.pi*(np.array([(b*x)%p for x in mu]).astype(float))/p).sum())**2 for b in range(1,p)])
    q=p; Mmax2=a2.max()
    print(f"n={n} p={p} beta={np.log(p)/np.log(n):.2f}: true max|eta|^2={Mmax2:.2f}")
    for r in range(1,7):
        qAr=(a2**r).sum()              # = sum_{b!=0}|eta|^{2r} = q*A_r
        qWick=q*dfact(2*r-1)*(n**r)     # conditional surrogate q*Wick
        # valid upper bound on max|eta|^2 from rung r:  (q*A_r)^{1/r}  [always valid]
        # conditional (using Wick): (q*Wick)^{1/r}  [valid ONLY if A_r<=Wick]
        ub_true=qAr**(1.0/r); ub_cond=qWick**(1.0/r)
        bad = qAr>qWick
        cond_invalid = ub_cond < Mmax2  # conditional bound BELOW true max => INVALID (false bound)
        print(f"  r={r}: (qA_r)^(1/r)={ub_true:.1f}  (qWick)^(1/r)={ub_cond:.1f}  A_r>Wick={bad}  cond_bound_INVALID(below true max)={cond_invalid}")

analyze(32,1217)
print("---control: clean prize prime---")
analyze(16,65537)
