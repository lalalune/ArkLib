# COUNTER-PROBE C: (1) extend marginal psi2-excess to LARGER t (tail regime where sub-Gaussian
# could fail). (2) The ACTUAL content of LEMMA (b) is the INCREMENT process: is |eta_b - eta_b'|
# sub-Gaussian with parameter ~ quotient distance? Probe the increment psi2-excess directly to
# CONFIRM the result's honest caveat (marginal != increment principle).
import numpy as np, sympy, math
def periods(p,n,cap=2_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap); reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p; eta=np.empty(M,dtype=complex); CH=10000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]; eta[i:i+b.shape[0]]=np.exp(1j*w*((b*mu)%p)).sum(axis=1)
    return eta,reps,mm
print("COUNTER C: marginal psi2-excess to LARGE t, + increment sub-Gaussianity (LEMMA b content).")
for (p,n) in [(786433,16),(13631489,32),(104857601,64)]:
    if (p-1)%n or not sympy.isprime(p): continue
    eta,reps,mm=periods(p,n); re=eta.real-eta.real.mean(); sig=re.std()
    z=re/sig
    # marginal psi2 excess at large t
    excs=[]
    for t in [1,2,3,4,5,6]:
        lm=math.log(np.mean(np.exp(t*z)))-t*t/2; excs.append((t,lm))
    beta=math.log(p)/math.log(n)
    print(f"\np={p} n={n} m={mm} beta={beta:.2f}  Var={re.var():.2f}(=n? {n})")
    print("  marginal log-MGF excess over t^2/2 (>0 = HEAVIER than Gaussian, sub-G FAILS):")
    print("   "+"  ".join(f"t={t}:{e:+.4f}" for t,e in excs))
    # increment: pick random pairs, measure D=|eta_b-eta_b'|, standardize, psi2 excess of increment marginal
    rng=np.random.default_rng(1); K=min(len(eta),200000)
    i1=rng.integers(0,len(eta),K); i2=rng.integers(0,len(eta),K)
    d=(eta[i1]-eta[i2]).real; d=d-d.mean(); ds=d.std(); zd=d/ds
    iexc=[]
    for t in [1,2,3,4]:
        lm=math.log(np.mean(np.exp(t*zd)))-t*t/2; iexc.append((t,lm))
    print(f"  increment (eta_b-eta_b').real std={ds:.2f}: standardized log-MGF excess:")
    print("   "+"  ".join(f"t={t}:{e:+.4f}" for t,e in iexc))
