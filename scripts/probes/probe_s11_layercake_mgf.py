import math, cmath
from sympy import primitive_root, nextprime

def spectrum(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); mu=[pow(h,j,p) for j in range(n)]
    ts=[];w=2*math.pi/p
    for b in range(1,p):
        s=0j
        for x in mu: s+=cmath.exp(1j*w*((b*x)%p))
        ts.append(abs(s)**2/n)
    return ts
def find_p(n,beta=4):
    p=nextprime(n**beta)
    while p<200000:
        if (p-1)%n==0 and (p-1)//n>=2 and p>n**3: return p
        p=nextprime(p)
    return None

# Verify the TWO-LEMMA decomposition:
# (L1) t^r <= r!/c^r * e^{ct}   [pointwise, for c>0, t>=0]
# (L2) sum t_b^r <= r!/c^r * sum e^{c t_b}
# (MGF) MGF(c):=(1/P) sum e^{c t_b}.  Then M_r <= r!/c^r * MGF(c).
# Compare to A(c)=sup S(s)e^cs from before. MGF should be a VALID (looser) tail constant.
for n in [16,32]:
    p=find_p(n)
    if not p: print(f"n={n}: no p"); continue
    ts=spectrum(n,p); P=len(ts)
    for c in [0.4,0.5,0.59]:
        MGF=sum(math.exp(c*t) for t in ts)/P
        print(f"n={n} p={p} c={c}: MGF(c)={MGF:.4f}")
        # L1 pointwise spot check
        l1ok=all((t**r) <= (math.factorial(r)/c**r)*math.exp(c*t)*(1+1e-9) for t in ts[:50] for r in range(1,7))
        allok=True
        for r in range(1,9):
            Mr=sum(t**r for t in ts)/P
            bound=(math.factorial(r)/c**r)*MGF
            ok=Mr<=bound*(1+1e-9); allok=allok and ok
        print(f"    L1 pointwise t^r<=r!/c^r e^ct: {l1ok}   M_r<=r!/c^r*MGF all r: {allok}")
