import cmath, math
def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def find_prime(n, beta):
    target=int(n**beta); k=max(1,(target-1)//n)
    while True:
        p=1+k*n
        if p>target and p>n**3 and is_prime(p) and (p-1)//n>1: return p
        k+=1
def gen(p):
    fac=[]; x=p-1; d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

# IDEA: the period eta_b is a LINEAR RECURRENCE / orbit sum under x->2x.
# Since n=2^mu, mu_n = {x: x^(2^mu)=1}. The map T: x -> x^2 is the DOUBLING; it acts on mu_n
# as a nilpotent-mod-1 shift (every element has 2-power order). eta_b = sum over the T-orbit
# structure. KEY TEST: write eta_b via the 2-adic ODOMETER. The exponents of h (generator of mu_n)
# are j=0..n-1; x->x^2 is j->2j mod n on the EXPONENTS = the binary ODOMETER/adding machine?
# No: 2j mod n on Z/2^mu is the one-sided shift (drop top bit). So mu_n under squaring = the
# one-sided 2-shift = the doubling map on the 2-adic integers Z_2 / 2^mu Z_2.
# eta_b = sum over the FULL shift space (cylinder) of e_p(b * h^j). This is a Birkhoff sum!
# TEST: how concentrated is the worst c*? Compare the WORST single coset to a RANDOM one, and
# check if the worst b lies in a small-2-adic-complexity orbit.

for (n,beta) in [(16,4),(32,4),(64,4)]:
    p=find_prime(n,beta); g=gen(p); m=(p-1)//n
    h=pow(g,(p-1)//n,p)
    w=2j*math.pi/p
    S=[pow(h,j,p) for j in range(n)]
    # compute all periods, find worst coset c*
    eta=[sum(cmath.exp(w*((pow(g,c,p)*x)%p)) for x in S) for c in range(m)]
    av=[abs(e) for e in eta]
    cstar=max(range(m), key=lambda c: av[c])
    bstar=pow(g,cstar,p)
    M=av[cstar]
    # 2-adic structure of the worst b: orbit of b under b->2b mod p (the DUAL doubling)
    orb=set(); x=bstar
    for _ in range(2*n):
        orb.add(x); x=2*x%p
    # how many distinct values does |eta| concentrate near the max? (degeneracy of top resonance)
    srt=sorted(av,reverse=True)
    topgap=srt[0]-srt[1]
    # is the worst b a real-subspace / b with b and -b both extreme?
    bm=(p-bstar)%p; cm=None
    for c in range(m):
        if pow(g,c,p)==bm: cm=c; break
    print(f"n={n} p={p}: M={M:.2f} M/sqrt(n log p/n)={M/math.sqrt(n*math.log(p/n)):.3f}  top1-top2gap={topgap:.3f} (rel {topgap/M:.3f})  dual2adic_orbit_len={len(orb)}")
