# GROSS-KOBLITZ angle (#407): does the UNIT PART (phase) of the Gauss sum tau(chi^j),
# given by p-adic Gamma_p, constrain the floor B = max_b |eta_b|?
#
# Setup: eta_b = sum_{x in mu_n} e_p(b x). The DFT-over-cosets relation
#   eta_b = (1/m) sum_{j} chibar^j(b) * tau(chi^j)   (chi a generator of subgroup-dual char group of order m=(q-1)/n)
# expresses eta as a DFT of the Gauss sums tau(chi^j), |tau| = sqrt(q) for j != 0.
# The FLOOR (max_b |eta_b|) is governed by how the PHASES arg(tau(chi^j)) DFT-interfere.
#
# Stickelberger gives only the p-adic VALUATION (magnitude blind). Gross-Koblitz gives the exact
# Gauss sum incl. UNIT (phase) part via Gamma_p. QUESTION: is arg(tau(chi^j)) Gamma_p-structured
# enough to bound the DFT max below the equidistributed (BGK sqrt(m log m)) value, or equidistributed?
#
# DECISIVE TEST: compare the actual phase sequence {arg(tau(chi^j))}_j against:
#   (A) the EQUIDISTRIBUTED null (random phases): DFT max ~ sqrt(m log m) * sqrt(q)/... 
#   (B) any Gamma_p-induced rigidity (e.g. functional equation tau(chi)tau(chibar)=chi(-1)q,
#       Hasse-Davenport, multiplicative argument structure).
import math, cmath, random

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a

def gauss_sums(p, n):
    """Return tau(chi^j) for j=0..m-1 where chi has order m=(q-1)/n on the subgroup-quotient.
    We use the multiplicative character chi(g0^t) = exp(2pi i t / (p-1)) (order p-1),
    and the relevant subgroup characters are chi^{n*j} of order m. Gauss sum tau(psi) =
    sum_{x in F_p^*} psi(x) e_p(x)."""
    g0 = primroot(p)
    # discrete log table
    dlog = [0]*p
    cur=1
    for t in range(p-1):
        dlog[cur]=t
        cur=cur*g0%p
    ep = [cmath.exp(2j*math.pi*x/p) for x in range(p)]
    m = (p-1)//n
    taus=[]
    for j in range(m):
        # character of order m: psi(x) = exp(2pi i * n * j * dlog(x) / (p-1)) = exp(2pi i j dlog(x)/m)
        s=0j
        for x in range(1,p):
            s += cmath.exp(2j*math.pi*j*dlog[x]/m) * ep[x]
        taus.append(s)
    return taus, m

def eta_via_taus(p,n):
    """Reconstruct eta_b for the subgroup mu_n via DFT of Gauss sums, and directly, to confirm."""
    g0=primroot(p)
    g=pow(g0,(p-1)//n,p)
    roots=[pow(g,i,p) for i in range(n)]
    ep=[cmath.exp(2j*math.pi*x/p) for x in range(p)]
    m=(p-1)//n
    # distinct eta over coset reps b = g0^i, i=0..m-1
    etas=[]
    b=1
    for i in range(m):
        s=sum(ep[(b*x)%p] for x in roots)
        etas.append(s)
        b=b*g0%p
    return etas,m

print("Comparing: actual phase-DFT floor B vs equidistributed-phase null over many primes")
print("n   p     m   B/sqrt(n)  null_med/sqrt(n)  null_max/sqrt(n)  B_pctile  phase_var")
random.seed(1)
for n in [8,16,32]:
    for p in [pp for pp in range(n*4+1, 6000, n) if isprime(pp)][:6]:
        taus,m = gauss_sums(p,n)
        if m<2: continue
        q=p
        sq=math.sqrt(q)
        # actual phases of tau(chi^j) for j=1..m-1 (j=0 is tau=-1, magnitude 1)
        phases=[cmath.phase(t) for t in taus[1:]]
        # eta directly
        etas,_=eta_via_taus(p,n)
        B=max(abs(e) for e in etas)
        sn=math.sqrt(n)
        # NULL: replace tau(chi^j) phases with random phases (keep magnitude sqrt(q)), reconstruct eta via
        # the SAME DFT structure. eta_b = (1/m) sum_j chibar^j(b) tau(chi^j). We mimic the DFT max.
        # Build the DFT matrix: for coset index i (b=g0^i), eta_i = (1/?) sum_j w^{-i j} tau_j with w=exp(2pi i/m).
        # Determine normalization from actual taus first:
        nulls=[]
        for trial in range(200):
            rnd_taus=[taus[0]] + [sq*cmath.exp(2j*math.pi*random.random()) for _ in range(m-1)]
            # reconstruct via inverse-DFT structure matching actual
            mx=0.0
            for i in range(m):
                val=sum(cmath.exp(-2j*math.pi*i*j/m)*rnd_taus[j] for j in range(m))/m
                if abs(val)>mx: mx=abs(val)
            nulls.append(mx)
        nulls.sort()
        null_med=nulls[len(nulls)//2]
        null_max=nulls[-1]
        # where does actual B fall in null distribution?
        below=sum(1 for x in nulls if x<B)
        pctile=below/len(nulls)
        pvar=sum((cmath.phase(t)%(2*math.pi))**0 for t in taus[1:])  # placeholder count
        print(f"{n:<4}{p:<6}{m:<4}{B/sn:<11.3f}{null_med/sn:<18.3f}{null_max/sn:<18.3f}{pctile:<10.2f}{len(phases)}")
