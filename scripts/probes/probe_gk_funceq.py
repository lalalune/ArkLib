# What EXACT phase structure does Gross-Koblitz / Gamma_p actually give, and is it a handle?
# The classical RELATIONS on Gauss sum phases (consequences of Gross-Koblitz reflection/multiplication):
#  (1) tau(chi) * tau(chibar) = chi(-1) * q   => arg(tau(chi)) + arg(tau(chibar)) = arg(chi(-1)) in {0,pi}
#  (2) Hasse-Davenport product/lifting relations
#  (3) |tau(chi)| = sqrt(q) for nontrivial chi (the magnitude, already known)
# The UNIT part of Gross-Koblitz is essentially Gamma_p(a/(q-1)) which is a p-ADIC unit; its
# COMPLEX phase is what we need. KEY MATHEMATICAL POINT: Gross-Koblitz lives in C_p (p-adic), the
# phase relevant to the floor lives in C (archimedean). Gamma_p constrains the p-adic unit, NOT the
# complex argument directly. The only ARCHIMEDEAN constraints on phases are the func-eqs (1),(2).
#
# TEST: do the func-eq pairings (chi <-> chibar) reduce the DFT floor below equidistributed?
# i.e. impose the REAL constraint arg(tau_j)+arg(tau_{m-j}) = 0 or pi, random elsewhere.
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
    fac=set(); mm=p-1; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def gauss_sums(p,n):
    g0=primroot(p)
    dlog=[0]*p; cur=1
    for t in range(p-1):
        dlog[cur]=t; cur=cur*g0%p
    ep=[cmath.exp(2j*math.pi*x/p) for x in range(p)]
    m=(p-1)//n
    taus=[]
    for j in range(m):
        s=sum(cmath.exp(2j*math.pi*j*dlog[x]/m)*ep[x] for x in range(1,p))
        taus.append(s)
    return taus,m
def floor_from_taus(taus,m):
    mx=0.0
    for i in range(m):
        val=sum(cmath.exp(-2j*math.pi*i*j/m)*taus[j] for j in range(m))/m
        if abs(val)>mx: mx=abs(val)
    return mx

random.seed(7)
print("Testing whether func-eq phase constraint (chi<->chibar) lowers floor vs free-random")
print("n   p     m   B_actual  free_med  funceq_med  funceq_max  actual_pct_vs_funceq")
for n in [8,16,32]:
    for p in [pp for pp in range(n*4+1, 4000, n) if isprime(pp)][:5]:
        taus,m=gauss_sums(p,n)
        if m<3: continue
        sq=math.sqrt(p); sn=math.sqrt(n)
        B=floor_from_taus(taus,m)
        free=[]; funceq=[]
        for _ in range(300):
            # free random
            rt=[taus[0]]+[sq*cmath.exp(2j*math.pi*random.random()) for _ in range(m-1)]
            free.append(floor_from_taus(rt,m))
            # func-eq constrained: pick phase for j in 1..m//2, set j and m-j paired so
            # arg_j + arg_{m-j} = s*pi (s random 0/1), |tau|=sqrt(q)
            ph=[None]*m
            for j in range(1,m):
                if ph[j] is None:
                    jc=(m-j)%m
                    a=2*math.pi*random.random()
                    s=random.choice([0,math.pi])
                    ph[j]=a
                    if jc!=j:
                        ph[jc]=(s-a)
                    else:
                        ph[j]=s/2  # self-conjugate (real tau)
            ct=[taus[0]]+[sq*cmath.exp(1j*ph[j]) for j in range(1,m)]
            funceq.append(floor_from_taus(ct,m))
        free.sort(); funceq.sort()
        fmed=free[len(free)//2]; femed=funceq[len(funceq)//2]; femax=funceq[-1]
        below=sum(1 for x in funceq if x<B)/len(funceq)
        print(f"{n:<4}{p:<6}{m:<4}{B/sn:<10.3f}{fmed/sn:<10.3f}{femed/sn:<12.3f}{femax/sn:<12.3f}{below:.2f}")
