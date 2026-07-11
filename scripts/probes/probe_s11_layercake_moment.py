import math, cmath
from sympy import primitive_root, isprime, nextprime

def spectrum(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mu = [pow(h, j, p) for j in range(n)]
    ts=[]; w=2*math.pi/p
    for b in range(1,p):
        s=0j
        for x in mu: s += cmath.exp(1j*w*((b*x) % p))
        ts.append(abs(s)**2/n)
    return ts

def find_p(n, beta=4):
    p=nextprime(n**beta)
    while p<200000:
        if (p-1)%n==0 and (p-1)//n>=2 and p>n**3: return p
        p=nextprime(p)
    return None

# RIGOROUS layer-cake check:
# For a fixed rate c, the SMALLEST A making S(s)<=A e^{cs}... no: S(s)<=A e^{-cs} for ALL s
#   => A >= sup_s S(s) e^{cs}.  Take A(c)=sup_s S(s)e^{cs} over the discrete jumps (s=each t_b).
# Then the layer-cake THEOREM claims:  M_r = (1/P) sum t_b^r <= A(c) * r! / c^r.
# Verify this holds for ALL r with the rigorously-valid A(c).
for n in [16]:
    p=find_p(n)
    ts=sorted(spectrum(n,p)); P=len(ts)
    def Scount(s): 
        # survival as fraction (right-continuous: #{t>=s})
        import bisect
        idx=bisect.bisect_left(ts,s)
        return (P-idx)/P
    for c in [0.4,0.5,0.59,0.669,0.8]:
        # A(c) = sup over s of S(s) e^{cs}; sup attained at jump points (just below each distinct t)
        distinct=sorted(set(ts))
        A=0.0
        for s in [0.0]+distinct:
            val=Scount(s)*math.exp(c*s)
            if val>A: A=val
        print(f"n={n} p={p} c={c:.3f}  A(c)=sup S(s)e^cs = {A:.4f}")
        allok=True
        for r in range(1,9):
            Mr=sum(t**r for t in ts)/P
            bound=A*math.factorial(r)/c**r
            ok=Mr<=bound*(1+1e-9)
            allok=allok and ok
            print(f"     r={r}  M_r={Mr:10.3f}  A*r!/c^r={bound:12.3f}  ok={ok}")
        print(f"   => ALL r ok: {allok}\n")
