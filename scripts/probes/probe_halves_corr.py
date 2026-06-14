# Champion-vs-phaselock: are |phi(b)| and |phi(bg)| (the two tower-half sums) independent?
# phi(b) = eta over mu_{2^{mu-1}}; b ranges over cosets; g = level-mu coset rep.
# corr ~ 0  => halves decorrelated (probabilistic proof route viable); corr>0 => correlated.
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
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def v2(x):
    k=0
    while x%2==0: x//=2; k+=1
    return k
MUMAX=12
p=None; cand=(1<<MUMAX)*70+1
while cand<4_000_000:
    if isprime(cand) and v2(cand-1)>=MUMAX: p=cand; break
    cand+=(1<<MUMAX)
g0=primroot(p); gfull=pow(g0,(p-1)//(1<<MUMAX),p)
pe=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
print(f"p={p}, v2(p-1)={v2(p-1)}",flush=True)
print(f"{'mu':<4}{'corr(|phi(b)|^2,|phi(bg)|^2)':<30}{'phase-corr Re':<16}{'maxsum/(2max|phi|)':<20}",flush=True)
for mu in range(3, MUMAX+1):
    half=1<<(mu-1)
    step=1<<(MUMAX-mu)
    g=pow(gfull,step,p)                       # primitive 2^mu-th root
    subhalf=[pow(g,2*j%(1<<mu),p) for j in range(half)]  # mu_{2^{mu-1}} = <g^2>
    # cosets of mu_{2^{mu}}: reps g0^i, i=0..(p-1)/2^mu -1
    mcos=(p-1)//(1<<mu)
    xs=[]; ys=[]; phases=[]; maxphi=0.0; maxsum=0.0
    b=1
    for i in range(mcos):
        phib=sum(pe[(b*x)%p] for x in subhalf)
        phibg=sum(pe[(b*g*x)%p] for x in subhalf)
        ab=abs(phib); abg=abs(phibg)
        xs.append(ab*ab); ys.append(abg*abg)
        phases.append((phib.conjugate()*phibg).real/(ab*abg) if ab*abg>0 else 0)
        maxphi=max(maxphi,ab,abg); maxsum=max(maxsum,abs(phib+phibg))
        b=b*g0%p
    n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
    cov=sum((xs[i]-mx)*(ys[i]-my) for i in range(n))/n
    sx=(sum((v-mx)**2 for v in xs)/n)**.5; sy=(sum((v-my)**2 for v in ys)/n)**.5
    corr=cov/(sx*sy) if sx*sy>0 else 0
    avgphase=sum(phases)/n
    print(f"{mu:<4}{corr:<30.4f}{avgphase:<16.4f}{maxsum/(2*maxphi):<20.4f}",flush=True)
