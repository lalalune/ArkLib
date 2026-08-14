import math, cmath
from sympy import isprime, primitive_root

def mu_n(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    out, cur = [], 1
    for _ in range(n):
        out.append(cur); cur=(cur*h)%p
    assert len(set(out))==n
    return out

def eta(b,p,mu):
    s=0j
    for x in mu: s+=cmath.exp(2j*math.pi*((b*x)%p)/p)
    return s

def prime_for(n,beta):
    p=int(n**beta)|1
    while not (isprime(p) and (p-1)%n==0): p+=2
    return p

# KEY DECOUPLING IDEA: partition mu_n into cosets of mu_{n/L} (L dyadic sub-tower).
# l2-decoupling PREDICTS  ||eta||_{L^r} <~ (#caps)^? ( sum_caps ||eta_cap||_{L^r}^2 )^{1/2}.
# We measure the SQUARE-FUNCTION ratio: does sup_b |eta_b| <~ sqrt( sum_caps sup_b|eta_cap,b|^2 )?
# i.e. is the peak controlled by the l2-aggregate of sub-block peaks (the decoupling inequality
# at L^inf)? If the constant is O(polylog) and sub-block peaks are ~sqrt(n/L), we'd get
# M <~ sqrt(L) * sqrt(n/L)*polylog = sqrt(n)*polylog -- the FLOOR. Test the constant's growth.
print("n  L   M(n)    sqrt(sum subpeak^2)   ratio M/that    (subpeak avg)")
for n,beta in [(16,4),(32,4),(64,4),(64,5),(128,4)]:
    p=prime_for(n,beta); mu=mu_n(p,n)
    # full M (sample b over a coset-rich window for speed if huge; n small enough do partial)
    # exact M: scan all b (p can be ~ n^4 = 1.6e7 for n=64... too big). Use the known maximizer
    # structure: scan b over mu_n*small and a random-ish dense window.
    import random
    random.seed(1)
    # candidate b's: dilates of 1 and random
    cand=set(range(1,min(p,200000)))
    if p>200000:
        cand=set(random.randrange(1,p) for _ in range(200000)) | set(mu)
    M=0.0; bstar=1
    for b in cand:
        v=abs(eta(b,p,mu))
        if v>M: M=v; bstar=b
    # partition into L caps = cosets of mu_{n/L} ; take L=2 (the dyadic step): cap_j = coset reps
    L=2; sub=n//L
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    # mu_{sub} = <h^L>; cosets reps r_t = h^t, t=0..L-1
    musub=[pow(h,L*j,p) for j in range(sub)]
    reps=[pow(h,t,p) for t in range(L)]
    # subpeak_t = max_b | sum_{x in r_t * musub} e_p(bx) |, scanned over same cand
    subpeaks=[]
    for t in range(L):
        cap=[(reps[t]*x)%p for x in musub]
        sp=0.0
        for b in cand:
            s=0j
            for x in cap: s+=cmath.exp(2j*math.pi*((b*x)%p)/p)
            if abs(s)>sp: sp=abs(s)
        subpeaks.append(sp)
    sq=math.sqrt(sum(s*s for s in subpeaks))
    print(f"{n:3d} {L} {M:7.3f}  {sq:18.3f}   {M/sq:8.4f}     {sum(subpeaks)/L:.3f} (sqrt(n/L)={math.sqrt(sub):.2f})")
