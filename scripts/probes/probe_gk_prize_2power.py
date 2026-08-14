# FINAL: prize regime is n = 2^k (2-power subgroup mu_n). The relevant Gauss sums tau(chi^j) have
# chi of 2-power order m=(p-1)/n on the dual side. Test: are these phases pinned by Gamma_p?
#
# Gross-Koblitz for 2-power order chars: the Gamma_p product runs over base-p digits of a/(q-1).
# For the COMPLEX phase to be pinned we'd need the digit sum to land in a rational-phase class.
# Quadratic (order 2) is pinned (p mod 4). Order 4,8,... ARE there reflection/multiplication
# relations (Gauss/Jacobi, quartic reciprocity) but they involve a,b with p=a^2+b^2 -- the phase
# becomes a function of the REPRESENTATION p=a^2+b^2, an arithmetically WILD quantity, not a residue.
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); mm=p-1; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a

def order_m_tau(p,m):
    g0=primroot(p)
    dlog=[0]*p; cur=1
    for t in range(p-1):
        dlog[cur]=t; cur=cur*g0%p
    ep=[cmath.exp(2j*math.pi*x/p) for x in range(p)]
    s=sum(cmath.exp(2j*math.pi*dlog[x]/m)*ep[x] for x in range(1,p))
    return s

# quartic (m=4): p = 1 mod 4. arg pinned? compare to representation p=a^2+b^2
print("QUARTIC (m=4) Gauss sum phase vs p=a^2+b^2 representation")
print("p     a   b   arg(tau4)/pi   tau4/sqrt(p)")
def rep_sum2(p):
    for a in range(1,int(math.isqrt(p))+1):
        b2=p-a*a
        b=int(math.isqrt(b2))
        if b*b==b2: return a,b
    return None,None
for p in range(5,160):
    if isprime(p) and p%4==1:
        t=order_m_tau(p,4)
        a,b=rep_sum2(p)
        print(f"{p:<6}{a:<4}{b:<4}{cmath.phase(t)/math.pi:<15.4f}{t/math.sqrt(p):.4f}")

print()
# Octic (m=8): the actual structure for n=mu_8-ish. equidistributed?
import statistics
print("OCTIC (m=8): are phases equidistributed? Kolmogorov-style spread of arg/2pi in [0,1)")
oct_ph=[]
for p in range(17,3000):
    if isprime(p) and p%8==1:
        t=order_m_tau(p,8)
        oct_ph.append((cmath.phase(t)/(2*math.pi))%1.0)
# bin into 10 buckets
buckets=[0]*10
for x in oct_ph:
    buckets[min(9,int(x*10))]+=1
print(f"  N={len(oct_ph)} primes; phase/(2pi) histogram (10 bins, expect ~uniform):")
print("  "+" ".join(f"{b:3d}" for b in buckets))
exp=len(oct_ph)/10
chi2=sum((b-exp)**2/exp for b in buckets)
print(f"  chi^2 (9 dof, uniform null) = {chi2:.2f}  (crit 16.9 at 5%); uniform => equidistributed phases")
